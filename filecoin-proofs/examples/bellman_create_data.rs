use storage_proofs_core::sector::SectorId;
use filecoin_proofs::types::{SealPreCommitOutput, PieceInfo};
use std::collections::HashMap;
use filecoin_proofs::constants::*;
use std::fs::{File,OpenOptions};
use std::path::{Path, PathBuf};
use chrono::Utc;
use mapr::MmapOptions;
use filecoin_hashers::Hasher;
use std::sync::atomic::{AtomicUsize, AtomicU64, Ordering};
use storage_proofs_porep::stacked::{
    StackedDrg,
};
use storage_proofs_core::cache_key::CacheKey;
use storage_proofs_core::drgraph::Graph;
use std::sync::{Arc, mpsc, Mutex, RwLock};
//use memmap2::MmapMut;
use mapr::MmapMut;
use storage_proofs_core::compound_proof::{self, CompoundProof};
use std::collections::VecDeque;
use std::thread;
use std::thread::{sleep_ms};
use rand::{Rng};
use filecoin_proofs::types::*;
use storage_proofs_porep::stacked::StackedCompound;
use std::time::{Instant};
use storage_proofs_core::settings;
use filecoin_proofs::parameters::{setup_params, public_params, winning_post_public_params};
use storage_proofs_core::merkle::{MerkleTreeTrait, BinaryMerkleTree, create_base_merkle_tree};
use filecoin_proofs::caches::{get_stacked_params, get_post_params};
use rand::rngs::OsRng;

use filecoin_proofs::{PrivateReplicaInfo, PublicReplicaInfo};
use merkletree::store::{Store, DiskStore, StoreConfig};
use std::fs::{create_dir_all, remove_dir_all};
use std::collections::BTreeMap;
use filecoin_proofs::api::winning_post::{generate_winning_post, verify_winning_post, generate_winning_post_sector_challenge};
use filecoin_proofs::api::seal::{seal_pre_commit_phase1, seal_pre_commit_phase2, seal_commit_phase1, seal_commit_phase2};
use filecoin_proofs::api::util::{
    get_base_tree_leafs, get_base_tree_size,
};
use filecoin_proofs::PoStType;
use std::env;
use std::os::unix::fs;
use filecoin_hashers::types::Domain;
use rand::seq::SliceRandom;
use filecoin_proofs::with_shape;
use anyhow::{ensure, Context, Result};
use storage_proofs_post::fallback::{FallbackPoSt, FallbackPoStCircuit, FallbackPoStCompound};
use storage_proofs_core::parameter_cache::CacheableParameters;
use storage_proofs_core::util::default_rows_to_discard;
use storage_proofs_core::api_version::{ApiFeature, ApiVersion};

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;

use std::io::prelude::*;

const FATAL_NOLOCK: &str = "error acquiring task lock";
const FATAL_RCVTSK: &str = "error receiving task";
const FIXED_API_VERSION: ApiVersion = ApiVersion::V1_1_0;

lazy_static! {
    //pub static ref DATA: MmapMut = file_backed_mmap_from_zeroes();
    pub static ref SECTOR_SIZE: String = get_sector_size_env();
    pub static ref SECTORS_FOR_COMMIT: Arc<RwLock<VecDeque<u64>>> = Arc::new(RwLock::new(VecDeque::new()));
    pub static ref METAS_FOR_COMMIT: Arc<RwLock<HashMap<u64, sector_meta>>> = Arc::new(RwLock::new(HashMap::new()));
    pub static ref POREP_CONFIG: PoRepConfig=get_PoRepConfig();
    pub static ref POST_CONFIG: PoStConfig=get_PostConfig();

    pub static ref STAGE_DATA_CACHED: Vec<u8>=create_data();
    //pub static ref TREE_D_CACHE: Arc<RwLock<HashMap<String, MerkleTree<<DefaultPieceHasher as Hasher>::Domain, <DefaultPieceHasher as Hasher>::Function>>>> = Arc::new(RwLock::new(HashMap::new()));
    //pub static ref PRIVATER_EPLICA_INFO: Arc<RwLock<BTreeMap<SectorId, PrivateReplicaInfo>>>=Arc::new(RwLock::new(BTreeMap::new()));
    pub static ref PROVER_ID: ProverId = get_prover_id();
    pub static ref PIECE_INFOS: PieceInfo = get_piece_info();
    pub static ref CACHE_TREE_D: bool=get_env_swicher("CT".to_string(), true);

}

pub fn get_env_swicher(name: String, def: bool) -> bool {
    let res = if let Ok(switch) = env::var(name.clone()) {
        if switch == "true" {
            true
        } else if switch == "false" {
            false
        }
        else {
            def
        }
    } else {
        def
    };
    info!("The switch of {:?} is set to {:?}", name, res);
    res
}

fn get_numeric_env(env_key: String, def: usize) -> usize {
    let res = if let Ok(num) = env::var(env_key) {
        if let Ok(num) = num.parse() {
            num
        } else {
            def
        }
    } else {
        def
    };
    res
}

fn get_sector_size_env() -> String {
    let def = "32G".to_string();
    let res = if let Ok(sector_size) = env::var("SECTOR_SIZE") {
        sector_size
    } else {
        def
    };
    info!("SECTOR_SIZE is {:?}", res);
    res
}

fn get_piece_info() ->PieceInfo {
    let piece_size = get_data_size();
    let tree = with_shape!(piece_size, created_cached_dt_tree);
    //let tree = created_cached_dt_tree();
    let mut commitment = [0; 32];
    let mut bytes = tree.root().into_bytes();
    commitment.copy_from_slice(&bytes);
    info!("The commitment is: {:?}", commitment);
    //let mut hashed_size = 64;
    //let h1 = piece_hash(&commitment, &commitment);
    //commitment.copy_from_slice(h1.as_ref());
    PieceInfo::new(commitment, UnpaddedBytesAmount(127)).unwrap()
}

fn get_post_ornot_env() -> bool {
    let def = false;
    let res = if let Ok(do_post) = env::var("DO_POST") {
        match do_post.as_str() {
            "true" => true,
            _ => false,
        }
    } else {
        def
    };
    res
}

fn get_data_size() -> u64 {
    let file_size = match (*SECTOR_SIZE).as_str(){
        "64G" => SECTOR_SIZE_64_GIB,
        "32G" => SECTOR_SIZE_32_GIB,
        "1G" => SECTOR_SIZE_1_GIB,
        "512M" => SECTOR_SIZE_512_MIB,
        "8M" => SECTOR_SIZE_8_MIB,
        _ => panic!("Unsupported sector size {:?}", (*SECTOR_SIZE)),
    };
    file_size
}

fn file_backed_mmap_from_zeroes() -> MmapMut {
    let data_size= get_data_size();
    let nodes = data_size / 32;
    let mut file: File = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(format!("./stacked-data-{:?}", Utc::now()))
        .unwrap();

    info!("generating zeroed data");
    file.set_len(32 * nodes as u64).unwrap();

    unsafe { MmapOptions::new().map_mut(&file).unwrap() }
}

fn create_data() -> Vec<u8> {
    let data_size= get_data_size();
    vec![0; data_size as usize]
}

pub struct sector_meta {
    pub prover_id: ProverId,
    pub ticket: Ticket,
    pub pre_commit: SealPreCommitOutput,
    pub cache_path_str: String,
}

static SECTOR_SEQ: AtomicU64 = AtomicU64::new(1);
static SEAL_COMMIT_NUM: AtomicUsize = AtomicUsize::new(0);


pub const NODE_SIZE: usize = 32;

fn get_prover_id() -> ProverId {
    let rng = &mut rand::thread_rng();
    //rng.gen()

    let mut prover_id=[0u8; 32];
    rng.fill(&mut prover_id[..]);
    prover_id[31] &= 0b0011_1111;
    prover_id
}

fn cache_porep_params<Tree: 'static + MerkleTreeTrait>(porep_config: PoRepConfig) {
    info!("PoRep params");

    let public_params = public_params(&porep_config).unwrap();

    {
        let circuit = <StackedCompound<Tree, DefaultPieceHasher> as CompoundProof<
            StackedDrg<Tree, DefaultPieceHasher>,
            _,
        >>::blank_circuit(&public_params);
        let _ = StackedCompound::<Tree, DefaultPieceHasher>::get_param_metadata(
            circuit,
            &public_params,
        );
    }
    {
        let circuit = <StackedCompound<Tree, DefaultPieceHasher> as CompoundProof<
            StackedDrg<Tree, DefaultPieceHasher>,
            _,
        >>::blank_circuit(&public_params);
        StackedCompound::<Tree, DefaultPieceHasher>::get_groth_params(
            Some(&mut OsRng),
            circuit,
            &public_params,
        )
            .expect("failed to get groth params");
    }
    {
        let circuit = <StackedCompound<Tree, DefaultPieceHasher> as CompoundProof<
            StackedDrg<Tree, DefaultPieceHasher>,
            _,
        >>::blank_circuit(&public_params);

        StackedCompound::<Tree, DefaultPieceHasher>::get_verifying_key(
            Some(&mut OsRng),
            circuit,
            &public_params,
        )
            .expect("failed to get verifying key");
    }
}

fn cache_winning_post_params<Tree: 'static + MerkleTreeTrait>(post_config: &PoStConfig) {
    info!("Winning PoSt params");

    let post_public_params = winning_post_public_params::<Tree>(post_config).unwrap();

    {
        let post_circuit: FallbackPoStCircuit<Tree> =
            <FallbackPoStCompound<Tree> as CompoundProof<
                FallbackPoSt<Tree>,
                FallbackPoStCircuit<Tree>,
            >>::blank_circuit(&post_public_params);
        let _ = <FallbackPoStCompound<Tree>>::get_param_metadata(post_circuit, &post_public_params)
            .expect("failed to get metadata");
    }
    {
        let post_circuit: FallbackPoStCircuit<Tree> =
            <FallbackPoStCompound<Tree> as CompoundProof<
                FallbackPoSt<Tree>,
                FallbackPoStCircuit<Tree>,
            >>::blank_circuit(&post_public_params);
        <FallbackPoStCompound<Tree>>::get_groth_params(
            Some(&mut OsRng),
            post_circuit,
            &post_public_params,
        )
            .expect("failed to get groth params");
    }
    {
        let post_circuit: FallbackPoStCircuit<Tree> =
            <FallbackPoStCompound<Tree> as CompoundProof<
                FallbackPoSt<Tree>,
                FallbackPoStCircuit<Tree>,
            >>::blank_circuit(&post_public_params);

        <FallbackPoStCompound<Tree>>::get_verifying_key(
            Some(&mut OsRng),
            post_circuit,
            &post_public_params,
        )
            .expect("failed to get verifying key");
    }
}

fn get_PoRepConfig() -> PoRepConfig {
    let sector_size = get_data_size();
    let config = PoRepConfig {
        sector_size: SectorSize(sector_size as u64),
        partitions: PoRepProofPartitions(*POREP_PARTITIONS.read().unwrap().get(&sector_size).unwrap()),
        porep_id: porep_id(),
        api_version: FIXED_API_VERSION,
        api_features: vec![ApiFeature::SyntheticPoRep],
    };
    with_shape!(sector_size, cache_porep_params, (config.clone()));

    config
}

fn get_PostConfig() -> PoStConfig {
    let sector_size = get_data_size();

    let config = PoStConfig {
        sector_size: SectorSize(sector_size),
        challenge_count: WINNING_POST_CHALLENGE_COUNT,
        sector_count: 1,
        typ: PoStType::Winning,
        priority: true,
        api_version: FIXED_API_VERSION
    };

    //with_shape!(sector_size, cache_winning_post_params, (&config));
    //get_post_params(&config);
    config
}

fn get_cache_folder() -> String {
    "./bell-cache".to_string()
}

fn get_cache_path(sector_id: u64) -> String {
    format!(
        "./bell-cache/filecoin-proofs-cache-{}",
        sector_id,
    )
}

fn created_cached_dt_tree<Tree: 'static + MerkleTreeTrait>() -> BinaryMerkleTree<DefaultPieceHasher> {
    let data = create_data();

    let sp = compound_proof::SetupParams {
        vanilla_params: setup_params(&POREP_CONFIG).unwrap(),
        partitions: Some(usize::from(POREP_CONFIG.partitions.0)),
        priority: false,
    };

    let compound_public_params = <StackedCompound<Tree, DefaultPieceHasher> as CompoundProof<
        StackedDrg<Tree, DefaultPieceHasher>,
        _,
    >>::setup(&sp).unwrap();

    let cache_path_str = get_cache_folder();
    info!("cache path is: {:?}", cache_path_str);
    create_dir_all(cache_path_str.clone());
    let cache_path: PathBuf = Path::new(&cache_path_str).into();



    let data_tree = {
        let base_tree_size = get_base_tree_size::<DefaultBinaryTree>((POREP_CONFIG).sector_size).unwrap();
        let base_tree_leafs = get_base_tree_leafs::<DefaultBinaryTree>(base_tree_size).unwrap();

        trace!(
            "seal phase 2: base tree size {}, base tree leafs {}, cached above base {}",
            base_tree_size,
            base_tree_leafs,
            default_rows_to_discard(base_tree_leafs, BINARY_ARITY)
        );

        let mut config = StoreConfig::new(
            cache_path,
            CacheKey::CommDTree.to_string(),
            default_rows_to_discard(base_tree_leafs, BINARY_ARITY),
        );

        info!("Data tree config: {:?}", config);
        create_base_merkle_tree::<BinaryMerkleTree<DefaultPieceHasher>>(
            Some(config.clone()),
            base_tree_leafs,
            &data,
        ).unwrap()
    };
    data_tree
}

fn copy_cached_tree_d(sector_id: u64) {
    let src_path = "../sc-02-data-tree-d.dat".to_string();
    let dst_path =  format!("{}/sc-02-data-tree-d.dat", get_cache_path(sector_id));
    info!("Data tree destination");
    //let dst_path = get_cache_path(sector_id);
    fs::symlink(src_path, dst_path);
    info!("Finish symbol link");
    //copy(src_path, dst_path);
}

fn get_staging_folder() -> String {
    "./bell-staging".to_string()
}

fn get_staging_path() -> String {
    "./bell-staging/singleton".to_string()
}

fn create_staging_file()
{
    let sector_bytes = PaddedBytesAmount::from(PaddedBytesAmount(get_data_size()));
    let in_path = get_staging_path();
    let f_data = OpenOptions::new().read(true).write(true).create(true).open(&in_path).unwrap();
    f_data.set_len(u64::from(sector_bytes)).unwrap();
    let mut staged_data = unsafe { MmapOptions::new().map_mut(&f_data).unwrap() };
    info!("data is generated");
}

fn porep_id() -> [u8; 32] {
    let mut porep_id = [0; 32];
    let registered_proof_id = 8u64;
    let nonce = 0u64;

    porep_id[0..8].copy_from_slice(&registered_proof_id.to_le_bytes());
    porep_id[8..16].copy_from_slice(&nonce.to_le_bytes());
    porep_id
}

fn get_sealed_folder() -> String {
    "./bell-sealed".to_string()
}

fn get_sealed_path(sector_id: u64) -> String {
    format!(
        "./bell-sealed/{}",
        sector_id,
    )

}

pub fn seal_pre_commit<Tree: 'static + MerkleTreeTrait>() {

    //let rng = &mut rand::thread_rng();

    let in_path = get_staging_path();

    let sector_id = 1;
    let out_path = get_sealed_path(sector_id);
    let _ = File::create(out_path.clone());

    let cache_path_str = get_cache_path(sector_id);
    info!("cache path is: {:?}", cache_path_str);
    create_dir_all(cache_path_str.clone());
    let cache_path: PathBuf = Path::new(&cache_path_str).into();

    let prover_id: ProverId = [0u8; 32];
    let ticket: Ticket = [0u8; 32];
    info!("Precommit ticket: {:?}", ticket);

    let phase1_start = Instant::now();
    let phase1_output= seal_pre_commit_phase1::<_,  _, _, Tree>(
        &POREP_CONFIG,
        cache_path.clone(),
        in_path,
        out_path.clone(),
        prover_id,
        SectorId::from(sector_id),
        ticket,
        &[(PIECE_INFOS.clone())],
    ).unwrap();
    info!("Precommit phase 1 takes {:?}", phase1_start.elapsed());

    let cache_path: PathBuf = Path::new(&cache_path_str).into();

    let phase2_start = Instant::now();
    let pre_commit = seal_pre_commit_phase2::<_,  _, Tree>(
        &POREP_CONFIG,
        phase1_output,
        cache_path,
        //Path::new(&get_staging_path().clone()),
        Path::new(&out_path.clone())).unwrap();
    info!("Precommit phase 2 takes {:?}", phase2_start.elapsed());

    let comm_d_path = format!("{}/comm_d", cache_path_str);
    let mut buffer = File::create(comm_d_path).unwrap();
    buffer.write(&pre_commit.comm_d).unwrap();

    let comm_r_path = format!("{}/comm_r", cache_path_str);
    let mut buffer = File::create(comm_r_path).unwrap();
    buffer.write(&pre_commit.comm_r).unwrap();

    let meta = sector_meta {
        prover_id,
        ticket,
        pre_commit,
        cache_path_str,
    };
    &(*SECTORS_FOR_COMMIT).write().unwrap().push_back(sector_id);
    &(*METAS_FOR_COMMIT).write().unwrap().insert(sector_id, meta);
}

pub fn seal_commit<Tree: 'static + MerkleTreeTrait>() {

    if &(*SECTORS_FOR_COMMIT).read().unwrap().len() > &0 {
        info!("There are ((((({:?}))))) sectors is ready for prove", &(*SECTORS_FOR_COMMIT).read().unwrap().len());
        let rng = &mut rand::thread_rng();

        let sector_id = &(*SECTORS_FOR_COMMIT).write().unwrap().pop_front().unwrap();
        let cache_path_str = get_cache_path(*sector_id);
        let cache_path: PathBuf = Path::new(&cache_path_str).into();
        let seed: Ticket = rng.gen();

        let meta =  &(*METAS_FOR_COMMIT).write().unwrap().remove(&sector_id).unwrap();
        let prover_id = meta.prover_id;
        let phase1_start = Instant::now();
        let phase1_output = seal_commit_phase1::<_, Tree>(
            &POREP_CONFIG,
            cache_path.clone(),
            Path::new(&get_sealed_path(*sector_id).clone()).into(),
            prover_id.clone(),
            SectorId::from(*sector_id),
            meta.ticket,
            seed,
            meta.pre_commit.clone(),
            &[PIECE_INFOS.clone()],
        ).unwrap();
        info!("Commit phase 1 takes {:?}", phase1_start.elapsed());

        let phase2_start = Instant::now();
        let _ = seal_commit_phase2::<Tree>(
            &POREP_CONFIG,
            phase1_output,
            prover_id,
            SectorId::from(*sector_id),
        ).unwrap();
        info!("Commit phase 2 takes {:?}", phase2_start.elapsed());

        info!("seal_commit:end");
        SEAL_COMMIT_NUM.fetch_add(1, Ordering::SeqCst);
        info!("##########################");
        info!("##########################");
        info!("Seal commit {:?} sectors!", SEAL_COMMIT_NUM.load(Ordering::SeqCst));
        info!("##########################");
        info!("##########################");

        info!("Finish prove");
        // (*PRIVATER_EPLICA_INFO).write().unwrap().insert(
        //     SectorId::from(*sector_id),
        //     PrivateReplicaInfo::new(Path::new(&get_sealed_path(*sector_id)).into()
        //                             , meta.pre_commit.comm_r, cache_path).unwrap(),
        // );
    }

}

pub fn post() {
    // if &(*PRIVATER_EPLICA_INFO).read().unwrap().len() == &0 {
    //     info!("No sector has been proved yet, don't do post");
    // } else {
    //     info!("!!!!!!!!!!!!!POST is started!!!!!!!!!!!!");
    //     let start_candidate = Instant::now();
    //     let rng = &mut rand::thread_rng();
    //     let mut randomness=[44u8; 32];
    //     rng.fill(&mut randomness[..]);
    //     randomness[31] &= 0b0000_0000;
    //     info!("Randomess for post is: {:?}", randomness);
    //     //let challenge_count : u64 =  ((&(*PRIVATER_EPLICA_INFO).read().unwrap().len()-1)/25+1) as u64;
    //     let challenge_count = ((&(*PRIVATER_EPLICA_INFO).read().unwrap().len()-1)/25+1) as u64;;
    //     info!("Challenge count for EPost is: {:?}", challenge_count);
    //     let prover_id = (*PROVER_ID).clone();
    //
    //     let priv_replica_info = &(*PRIVATER_EPLICA_INFO).read().unwrap().clone();
    //
    //
    //
    //
    //     let candidates = generate_candidates (&*POST_CONFIG,
    //                                           &randomness,
    //                                           challenge_count,
    //                                           priv_replica_info,
    //                                           prover_id).unwrap();
    //     info!("POST get candidates takes: {:?}", start_candidate.elapsed());
    //     let start_generate_post = Instant::now();
    //     let winner = candidates.choose(&mut rand::thread_rng());
    //     info!("The winner is: {:?}", winner);
    //     let mut winners = Vec::new();
    //     winners.push(winner.unwrap().clone());
    //     let proofs = generate_election_post(&*POST_CONFIG, &randomness, &(*PRIVATER_EPLICA_INFO).read().unwrap(), winners.clone(), prover_id ).unwrap();
    //     let mut winner_commitment=[0u8; 32];
    //     let safe_comm_r =  priv_replica_info[&winner.unwrap().sector_id].safe_comm_r().unwrap();
    //     winner_commitment.clone_from_slice(safe_comm_r.as_ref());
    //     let pub_replica_info= PublicReplicaInfo::new(winner_commitment).unwrap();
    //     let mut pub_replicas:BTreeMap<SectorId, PublicReplicaInfo> = BTreeMap::new();
    //     pub_replicas.insert(winner.unwrap().sector_id, pub_replica_info);
    //
    //     info!("POST gemerate takes: {:?}", start_generate_post.elapsed());
    //     let verify = verify_election_post(&*POST_CONFIG, &randomness, challenge_count, &proofs, &pub_replicas, &winners, prover_id);
    //     info!("------POST verification result : {:?}------", verify);
    // }
    //

}

pub enum SealInput {
    pre_commit(),
    Shutdown,
}

pub enum ProveInput {
    commit(),
    Shutdown,
}

pub enum PostInput {
    post(),
    Shutdown,
}

pub struct SealWorker {
    pub id: usize,
    pub thread: Option<thread::JoinHandle<()>>,
}

pub struct ProveWorker {
    pub id: usize,
    pub thread: Option<thread::JoinHandle<()>>,
}

pub struct PostWorker {
    pub id: usize,
    pub thread: Option<thread::JoinHandle<()>>,
}

impl SealWorker {
    pub fn start(
        id: usize,
        seal_task_rx: Arc<Mutex<mpsc::Receiver<SealInput>>>,
    ) -> SealWorker
    {
        let thread = thread::spawn(move || loop {

            let task = {
                let rx = seal_task_rx.lock().expect(FATAL_NOLOCK);
                rx.recv().expect(FATAL_RCVTSK)
            };

            // Dispatch to the appropriate task-handler.
            match task {
                SealInput::pre_commit() => {
                    let sector_size = get_data_size();
                    with_shape!(sector_size, seal_pre_commit);
                }

                SealInput::Shutdown => break,
            }
        });

        SealWorker {
            id,
            thread: Some(thread),
        }
    }
}

impl ProveWorker {
    pub fn start(
        id: usize,
        prove_task_rx: Arc<Mutex<mpsc::Receiver<ProveInput>>>,
    ) -> ProveWorker
    {
        let thread = thread::spawn(move || loop {

            let task = {
                let rx = prove_task_rx.lock().expect(FATAL_NOLOCK);
                rx.recv().expect(FATAL_RCVTSK)
            };

            // Dispatch to the appropriate task-handler.
            match task {
                ProveInput::commit() => {
                    let sector_size = get_data_size();
                    with_shape!(sector_size, seal_commit);
                }

                ProveInput::Shutdown => break,
            }
        });

        ProveWorker {
            id,
            thread: Some(thread),
        }
    }
}

impl PostWorker {
    pub fn start(
        id: usize,
        post_task_rx: Arc<Mutex<mpsc::Receiver<PostInput>>>,
    ) -> PostWorker
    {
        let thread = thread::spawn(move || loop {

            let task = {
                let rx = post_task_rx.lock().expect(FATAL_NOLOCK);
                rx.recv().expect(FATAL_RCVTSK)
            };

            // Dispatch to the appropriate task-handler.
            match task {
                PostInput::post() => {
                    let sector_size = get_data_size();
                    //with_shape!(sector_size, post);
                }

                PostInput::Shutdown => break,
            }
        });

        PostWorker {
            id,
            thread: Some(thread),
        }
    }
}

pub fn start_seal(seal_num_worker: usize, seal_interval: usize, total_task_num: usize, waiting_count: usize)
{
    let (seal_tx, seal_workers) = {
        let (tx, rx) = mpsc::channel();
        let rx = Arc::new(Mutex::new(rx));

        let workers: Vec<SealWorker> = (0..seal_num_worker)
            .map(|n| {
                SealWorker::start(
                    n as usize,
                    rx.clone(),
                )
            })
            .collect();

        (tx, workers)
    };
    let mut count = 0;
    loop {
        if (count < total_task_num) && (waiting_count>=(*SECTORS_FOR_COMMIT).read().unwrap().len()) {
            let t = SealInput::pre_commit();
            seal_tx.clone().send(t).expect("Seal send error");
            count = count+1;
        }
        sleep_ms((seal_interval*1000) as u32);
    }

}

pub fn start_prove(prove_num_worker: usize, prove_interval: usize)
{
    let (prove_tx, prove_workers) = {
        let (tx, rx) = mpsc::channel();
        let rx = Arc::new(Mutex::new(rx));

        let workers: Vec<ProveWorker> = (0..prove_num_worker)
            .map(|n| {
                ProveWorker::start(
                    n as usize,
                    rx.clone(),
                )
            })
            .collect();

        (tx, workers)
    };
    let start = Instant::now();

    loop {
        let t = ProveInput::commit();
        prove_tx.clone().send(t).expect("Prove send error");
        sleep_ms((prove_interval*1000) as u32);
    }
}

pub fn start_post(post: bool, post_interval: usize)
{
    let (post_tx, post_workers) = {
        let (tx, rx) = mpsc::channel();
        let rx = Arc::new(Mutex::new(rx));

        let workers: Vec<PostWorker> = (0..1)
            .map(|n| {
                PostWorker::start(
                    n as usize,
                    rx.clone(),
                )
            })
            .collect();

        (tx, workers)
    };
    let start = Instant::now();

    loop {
        if post {
            let t = PostInput::post();
            post_tx.clone().send(t).expect("Post send error");
        }

        sleep_ms((post_interval*1000) as u32);
    }
}


fn main() {
    fil_logger::init();

    let seal_num_worker: usize = get_numeric_env("PRECOMMIT_COUNT".to_string(), 1);
    info!("PRECOMMIT_COUNT is {:?}", seal_num_worker);
    let prove_num_worker: usize = get_numeric_env("COMMIT_COUNT".to_string(), 1);
    info!("COMMIT_COUNT is {:?}", prove_num_worker);
    let total_task_num: usize = get_numeric_env("TOTAL_TASKS".to_string(), 1);
    info!("TOTAL_TASKS is {:?}", total_task_num);
    let seal_interval: usize = get_numeric_env("PRECOMMIT_INTERVAL".to_string(), 60);
    info!("PRECOMMIT_INTERVAL is {:?}", seal_interval);
    let prove_interval: usize = get_numeric_env("COMMIT_INTERVAL".to_string(), 60);
    info!("COMMIT_INTERVAL is {:?}", prove_interval);
    let do_post = get_post_ornot_env();
    info!("DO_POST is {:?}", do_post);
    let post_interval: usize = get_numeric_env("POST_INTERVAL".to_string(), 15);
    info!("POST_INTERVAL is {:?}", post_interval);

    let waiting_count: usize = get_numeric_env("WAITING_COUNT".to_string(), 2);
    info!("WAITING_COUNT set for waiting for prove count is {:?}", waiting_count);

    let staging_folder = get_staging_folder();
    //remove_dir_all(staging_folder.clone());
    create_dir_all(staging_folder.clone());
    create_staging_file();

    let sealed_folder = get_sealed_folder();
    //remove_dir_all(sealed_folder.clone());
    create_dir_all(sealed_folder.clone());

    let cache_folder = get_cache_folder();
    //remove_dir_all(cache_folder.clone());
    create_dir_all(cache_folder.clone());


    let _ = (*POREP_CONFIG).clone();
    let _ = (*POST_CONFIG).clone();
    let sector_size = get_data_size();

    with_shape!(sector_size, seal_pre_commit);
    for _ in (1..100) {
        with_shape!(sector_size, seal_commit);
    }
}