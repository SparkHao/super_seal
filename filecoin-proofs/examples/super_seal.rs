use storage_proofs_core::sector::SectorId;
use filecoin_proofs::types::{SealPreCommitOutput, PieceInfo};
use std::collections::HashMap;
use filecoin_proofs::constants::*;
use std::fs::{File,OpenOptions};
use std::path::{Path, PathBuf};
use chrono::Utc;
//use memmap::MmapOptions;
use mapr::MmapOptions;
use filecoin_hashers::Hasher;
use std::sync::atomic::{AtomicUsize, AtomicU64, Ordering};
use storage_proofs_porep::stacked::{
    StackedDrg,
};
use storage_proofs_core::cache_key::CacheKey;
use storage_proofs_core::drgraph::Graph;
use std::sync::{Arc, mpsc, Mutex, RwLock};
//use memmap::MmapMut;
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
use filecoin_proofs::parameters::{setup_params, public_params, winning_post_public_params, window_post_public_params};
use storage_proofs_core::merkle::{MerkleTreeTrait, BinaryMerkleTree, create_base_merkle_tree};
use filecoin_proofs::caches::{get_stacked_params, get_post_params};
use rand::rngs::OsRng;

use filecoin_proofs::{PrivateReplicaInfo, PublicReplicaInfo, generate_window_post, verify_window_post, get_seal_inputs, clear_caches};
use merkletree::store::{Store, DiskStore, StoreConfig};
use std::fs::{create_dir_all, remove_dir_all};
use std::collections::BTreeMap;
use filecoin_proofs::api::winning_post::{generate_winning_post, verify_winning_post, generate_winning_post_sector_challenge};

use filecoin_proofs::api::seal::{seal_pre_commit_phase1, seal_pre_commit_phase2, seal_commit_phase1, seal_commit_phase2, aggregate_seal_commit_proofs, verify_aggregate_seal_commit_proofs,};
use filecoin_proofs::api::util::{
    get_base_tree_leafs, get_base_tree_size,
};
use storage_proofs_core::util::default_rows_to_discard;
use storage_proofs_core::settings::*;
use filecoin_proofs::PoStType;
use std::env;
use std::os::unix::fs;
use filecoin_hashers::types::Domain;
use rand::seq::SliceRandom;
use filecoin_proofs::with_shape;
use anyhow::{ensure, Context, Result};
use storage_proofs_post::fallback::{FallbackPoSt, FallbackPoStCircuit, FallbackPoStCompound};
use storage_proofs_core::parameter_cache::CacheableParameters;
use std::panic;
use std::io::{Write, Read};
use std::fs::remove_file;
use std::env::set_var;
use std::str::FromStr;
use bellperson::groth16;
use storage_proofs_core::api_version::{ApiFeature, ApiVersion};

extern crate rand;


#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;

const FATAL_NOLOCK: &str = "error acquiring task lock";
const FATAL_RCVTSK: &str = "error receiving task";

const LAST_SECTOR_ID: &str = "LAST_SECTOR_ID";
const FIXED_API_VERSION: ApiVersion = ApiVersion::V1_1_0;
const CC_PREFIX: &str = "LOTUS_CC_SECTOR_";
const API_FEATURES: [&str; 2] = ["synthetic-porep", "non-interactive-porep"];

lazy_static! {
    //pub static ref DATA: MmapMut = file_backed_mmap_from_zeroes();
    pub static ref SECTOR_SIZE: String = get_sector_size_env();
    pub static ref SECTORS_FOR_PROVE: Arc<RwLock<VecDeque<u64>>> = Arc::new(RwLock::new(VecDeque::new()));
    pub static ref SECTORS_FOR_HASH: Arc<RwLock<VecDeque<u64>>> = Arc::new(RwLock::new(VecDeque::new()));
    pub static ref METAS_FOR_PROVE: Arc<RwLock<HashMap<u64, sector_meta_precommit_output>>> = Arc::new(RwLock::new(HashMap::new()));
    pub static ref METAS_FOR_HASH: Arc<RwLock<HashMap<u64, sector_meta_precommit_phase1_output>>> = Arc::new(RwLock::new(HashMap::new()));

    pub static ref POREP_CONFIG: PoRepConfig=get_PoRepConfig();
    pub static ref WINNING_POST_CONFIG: PoStConfig=get_WinningPostConfig();
    pub static ref WINDOW_POST_CONFIG: PoStConfig=get_WindowConfig();

    pub static ref STAGE_DATA_CACHED: Vec<u8>=create_data();
    pub static ref REPLICA_INFO_FIELDS_MAP: Arc<RwLock<HashMap<u64, replica_info_fields>>>=Arc::new(RwLock::new(HashMap::new()));
    pub static ref PROVER_ID: ProverId = get_prover_id();
    pub static ref PIECE_INFOS: PieceInfo = get_piece_info();
    pub static ref CACHE_TREE_D: bool=get_env_swicher("CT".to_string(), false);

    pub static ref TEST_WINNING: bool = get_post_ornot_env();
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

fn porep_id() -> [u8; 32] {
    let mut porep_id = [0; 32];
    let registered_proof_id = 8u64;
    let nonce = 0u64;

    porep_id[0..8].copy_from_slice(&registered_proof_id.to_le_bytes());
    porep_id[8..16].copy_from_slice(&nonce.to_le_bytes());
    porep_id
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
    let def = "512M".to_string();
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
    let res = if let Ok(do_post) = env::var("WINNING") {
        match do_post.as_str() {
            "true" => true,
            _ => false,
        }
    } else {
        def
    };
    res
}

fn get_bellman_ornot_env() -> bool {
    let def = false;
    let res = if let Ok(do_post) = env::var("DO_BELLMAN") {
        match do_post.as_str() {
            "true" => true,
            _ => false,
        }
    } else {
        def
    };
    res
}

fn get_restart_ornot_env() -> bool {
    let def = true;
    let res = if let Ok(do_post) = env::var("RESTART") {
        match do_post.as_str() {
            "true" => true,
            _ => false,
        }
    } else {
        def
    };
    res
}

fn get_last_sector_id() -> usize {
    let sector_save_path = Path::new("./cache").join("last_sector_id");
    let file = OpenOptions::new()
        .write(true)
        .read(true)
        .create(true)
        .open(sector_save_path);
    if file.is_ok() {
        let mut sector_str = std::string::String::new();
        if file.is_ok() {
            let _ = file.unwrap().read_to_string(&mut sector_str);
            info!("sector_str = {:?}", sector_str.clone());
            if sector_str != "" {
                if sector_str.ends_with("\n") {
                    sector_str.truncate(sector_str.len() - 1);
                }
                if sector_str.ends_with(",") {
                    sector_str.truncate(sector_str.len() - 1);
                }
                info!("----sector_str = {:?}", sector_str);
                let sector_ids: Vec<&str> = sector_str.split(",").collect();
                info!("----arr = {:?}, len(): {}", sector_ids, sector_ids.len());
                return sector_ids.len();
            }
        }
    }
    0
}

fn set_last_sector_id(sector_id: &u64) {
    let sector_save_path = Path::new("./cache").join("last_sector_id");
    // remove_file(&sector_save_path);
    let mut file = OpenOptions::new()
        .write(true)
        .read(true)
        .create(true)
        .open(sector_save_path).unwrap();

    let mut value = String::new();
    file.read_to_string(&mut value);
    info!("-----------read data: {:?}", &value);
    let new_value = sector_id.to_string() + ",";
    info!("---set sector_id str: {:?}", &new_value);
    file.write(new_value.as_bytes());
}

fn get_data_size() -> u64 {
    let file_size = match (*SECTOR_SIZE).as_str(){
        "64G" => SECTOR_SIZE_64_GIB,
        "32G" => SECTOR_SIZE_32_GIB,
        "1G" => SECTOR_SIZE_1_GIB,
        "512M" => SECTOR_SIZE_512_MIB,
        "8M" => SECTOR_SIZE_8_MIB,
        "2K" => SECTOR_SIZE_2_KIB,
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

pub struct sector_meta_precommit_output {
    pub prover_id: ProverId,
    pub ticket: Ticket,
    pub pre_commit: SealPreCommitOutput,
    pub cache_path_str: String,
}

pub struct sector_meta_precommit_phase1_output {
    pub prover_id: ProverId,
    pub ticket: Ticket,
    pub labels_string: String,
    pub config_string: String,
    pub comm_d_string: String,
    pub cache_path_str: String,
}

pub struct replica_info_fields {
    pub replica: PathBuf,
    pub comm_r: Commitment,
    pub cache_dir: PathBuf,
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

fn cache_window_post_params<Tree: 'static + MerkleTreeTrait>(post_config: &PoStConfig) {
    info!("Window PoSt params");

    let post_public_params = window_post_public_params::<Tree>(post_config).unwrap();

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


fn get_WinningPostConfig() -> PoStConfig {
    let sector_size = get_data_size();

    let winning_config = PoStConfig {
        sector_size: SectorSize(sector_size),
        challenge_count: WINNING_POST_CHALLENGE_COUNT,
        sector_count: 1,
        typ: PoStType::Winning,
        priority: true,
        api_version: FIXED_API_VERSION,
    };

    with_shape!(sector_size, cache_winning_post_params, (&winning_config));
    //get_post_params(&winning_config);
    info!("winning_config is {:?}", winning_config);
    winning_config
}

fn get_WindowConfig() -> PoStConfig {
    let sector_size = get_data_size();

    let window_config = PoStConfig {
        sector_size: SectorSize(sector_size),
        challenge_count: WINDOW_POST_CHALLENGE_COUNT,
        sector_count: *WINDOW_POST_SECTOR_COUNT
            .read()
            .unwrap()
            .get(&sector_size)
            .unwrap(),
        typ: PoStType::Window,
        priority: true,
        api_version: FIXED_API_VERSION,
    };

    with_shape!(sector_size, cache_window_post_params, (&window_config));
    //get_post_params(&window_config);
    info!("window_config is {:?}", window_config);
    window_config
}

fn get_cache_folder() -> String {
    "./cache".to_string()
}

fn get_cache_path(sector_id: u64) -> String {
    format!(
        "./cache/filecoin-proofs-cache-{}",
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
        let base_tree_size = get_base_tree_size::<DefaultBinaryTree>((*POREP_CONFIG).sector_size).unwrap();
        let base_tree_leafs = get_base_tree_leafs::<DefaultBinaryTree>(base_tree_size).unwrap();

        trace!(
            "base tree size {}, base tree leafs {}, cached above base {}",
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
    info!("Create data tree is done!");
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
    "./staging".to_string()
}

fn get_staging_path() -> String {
    "./staging/singleton".to_string()
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

fn get_sealed_folder() -> String {
    "./sealed".to_string()
}

fn get_sealed_path(sector_id: u64) -> String {
    format!(
        "./sealed/{}",
        sector_id,
    )

}

pub fn precommit_phase1<Tree: 'static + MerkleTreeTrait>()
{

    let rng = &mut rand::thread_rng();

    let in_path = get_staging_path();

    let sector_id = SECTOR_SEQ.fetch_add(1, Ordering::SeqCst);


    let env_variable = format!("{}{}", CC_PREFIX, sector_id);
    set_var(env_variable, "true");

    let out_path = get_sealed_path(sector_id);
    let _ = File::create(out_path.clone());

    let cache_path_str = get_cache_path(sector_id);
    info!("cache path is: {:?}", cache_path_str);
    create_dir_all(cache_path_str.clone());
    let cache_path: PathBuf = Path::new(&cache_path_str).into();

    // let prover_id: ProverId = (*PROVER_ID).clone();
    //let ticket: Ticket = rng.gen();
    let prover_id: ProverId = [0u8; 32];
    let mut ticket= [0u8; 32];
    // rng.fill(&mut ticket[..]);
    // ticket[31] &= 0b0011_1111;

    copy_cached_tree_d(sector_id);

    let phase1_start = Instant::now();
    info!("prover_id = {:?}, SectorId = {:?}, ticket = {:?}", prover_id, sector_id, ticket);
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

    let labels_string = serde_json::to_string(&phase1_output.labels).unwrap();
    let config_string = serde_json::to_string(&phase1_output.config).unwrap();
    let comm_d_string = serde_json::to_string(&phase1_output.comm_d).unwrap();

    //let phase1_output_string = serde_json::to_string(&phase1_output).unwrap();

    let meta = sector_meta_precommit_phase1_output {
        prover_id,
        ticket,
        labels_string,
        config_string,
        comm_d_string,
        cache_path_str,
    };

    info!("replication VDE is done");
    &(*SECTORS_FOR_HASH).write().unwrap().push_back(sector_id);
    &(*METAS_FOR_HASH).write().unwrap().insert(sector_id, meta);
    println!("Finish sector {:?} precommit1 @{:?}", sector_id, Instant::now());
    // if sector_id % 3 == 0 {
    //     reset_settings("OPTION14", "1");
    //     reset_settings("OPTION15", "1");
    //     reset_settings("OPTION17", "0");
    //     reset_settings("OPTION6", "[0]");
    // }
    // if sector_id % 3 == 1 {
    //     reset_settings("OPTION14", "0");
    //     reset_settings("OPTION15", "0");
    //     reset_settings("OPTION17", "1");
    //     reset_settings("OPTION12", "true");
    // }
    // if sector_id % 3 == 2 {
    //     reset_settings("OPTION14", "1");
    //     reset_settings("OPTION15", "0");
    //     reset_settings("OPTION17", "0");
    // }

    if sector_id == 5 {
        // reset_settings("OPTION4", "true");
        // reset_settings("OPTION12", "false");
        // reset_settings("OPTION14", "1");
        // reset_settings("OPTION15", "1");
        // reset_settings("OPTION17", "0");
    }

    if sector_id == 10 {
        // reset_settings("OPTION4", "false");
        // reset_settings("OPTION12", "true");
        // reset_settings("OPTION14", "0");
        // reset_settings("OPTION15", "0");
        // reset_settings("OPTION17", "1");
    }
    //
    if sector_id == 15 {
        // reset_settings("OPTION12", "false");
        // reset_settings("OPTION4", "true");
        // reset_settings("OPTION14", "1");
        // reset_settings("OPTION15", "0");
        // reset_settings("OPTION17", "0");
    }
}

pub fn precommit_phase2<Tree: 'static + MerkleTreeTrait>() {
    info!("There are {:?} sectors waiting for precommit phase2", &(*SECTORS_FOR_HASH).read().unwrap().len());
    if &(*SECTORS_FOR_HASH).read().unwrap().len() > &0 {
        let sector_id = (*SECTORS_FOR_HASH).write().unwrap().pop_front().unwrap();
        let phase1_meta =  (*METAS_FOR_HASH).write().unwrap().remove(&sector_id).unwrap();
        let out_path = get_sealed_path(sector_id);
        let cache_path: PathBuf = Path::new(&phase1_meta.cache_path_str).into();

        let labels :Labels<Tree> = serde_json::from_str(&phase1_meta.labels_string).unwrap();
        let config :StoreConfig = serde_json::from_str(&phase1_meta.config_string).unwrap();
        let comm_d :Commitment = serde_json::from_str(&phase1_meta.comm_d_string).unwrap();

        let phase1_output = SealPreCommitPhase1Output::<Tree> {
            labels,
            config,
            comm_d,
        };

        let phase2_start = Instant::now();
        let pre_commit = seal_pre_commit_phase2::<_,  _, Tree>(
            &POREP_CONFIG,
            phase1_output,
            cache_path.clone(),
            //Path::new(&get_staging_path().clone()),
            Path::new(&out_path.clone())).unwrap();
        info!("Precommit phase 2 takes {:?}", phase2_start.elapsed());


        let comm_r = pre_commit.comm_r.clone();
        let meta = sector_meta_precommit_output {
            prover_id: phase1_meta.prover_id,
            ticket: phase1_meta.ticket,
            pre_commit,
            cache_path_str: phase1_meta.cache_path_str,
        };
        &(*SECTORS_FOR_PROVE).write().unwrap().push_back(sector_id);
        &(*METAS_FOR_PROVE).write().unwrap().insert(sector_id, meta);

        println!("Finish sector {:?} precommit2 @{:?}", sector_id, Instant::now());

        if *TEST_WINNING{
            &(*REPLICA_INFO_FIELDS_MAP).write().unwrap().insert(sector_id,
                                                                replica_info_fields {
                                                                    replica: Path::new(&out_path).into(),
                                                                    comm_r,
                                                                    cache_dir: Path::new(&cache_path).into(),
                                                                }
            );
        }

    }
}


pub fn seal_commit<Tree: 'static + MerkleTreeTrait>(do_bellman: bool) {

    if &(*SECTORS_FOR_PROVE).read().unwrap().len() > &0 {
        info!("There are ((((({:?}))))) sectors is ready for prove", &(*SECTORS_FOR_PROVE).read().unwrap().len());
        let rng = &mut rand::thread_rng();

        let sector_id = &(*SECTORS_FOR_PROVE).write().unwrap().pop_front().unwrap();
        let cache_path_str = get_cache_path(*sector_id);
        let cache_path: PathBuf = Path::new(&cache_path_str).into();
        //let seed: Ticket = rng.gen();

        let mut seed=[0u8; 32];
        rng.fill(&mut seed[..]);
        seed[31] &= 0b0011_1111;

        let meta =  &(*METAS_FOR_PROVE).write().unwrap().remove(&sector_id).unwrap();
        let prover_id = meta.prover_id;
        let phase1_start = Instant::now();
        let phase1_output = panic::catch_unwind(|| {
            info!("Start commit phase1 for sector {:?}", *sector_id);
            let res = seal_commit_phase1::<_, Tree>(
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
            res
        });


        if do_bellman {
            let phase2_start = Instant::now();
            if phase1_output.is_ok() {
                let phase1_output = phase1_output.unwrap();
                let commit_input = get_seal_inputs::<Tree>(
                    &POREP_CONFIG,
                    phase1_output.comm_r.clone(),
                    phase1_output.comm_d.clone(),
                    prover_id.clone(),
                    SectorId::from(*sector_id),
                    phase1_output.ticket.clone(),
                    phase1_output.seed.clone(),
                ).unwrap();


                let commit_output = seal_commit_phase2::<Tree>(
                    &POREP_CONFIG,
                    phase1_output,
                    prover_id,
                    SectorId::from(*sector_id),
                ).unwrap();

                let start = Instant::now();
                let num_proofs_to_aggregate = 16;
                let mut commit_outputs = Vec::with_capacity(num_proofs_to_aggregate);
                let mut commit_inputs = Vec::with_capacity(num_proofs_to_aggregate);
                let mut seeds = Vec::with_capacity(num_proofs_to_aggregate);



                for _ in 0..num_proofs_to_aggregate {
                    commit_outputs.push(commit_output.clone());
                    commit_inputs.extend(commit_input.clone());
                    seeds.push(seed.clone());
                }

                let aggregate_proof =
                    aggregate_seal_commit_proofs::<Tree>(&POREP_CONFIG, &seeds, &seeds, commit_outputs.as_slice(), groth16::aggregate::AggregateVersion::V1).unwrap();
                let res = verify_aggregate_seal_commit_proofs::<Tree>(&POREP_CONFIG, aggregate_proof, &seeds, &seeds, commit_inputs, groth16::aggregate::AggregateVersion::V1).unwrap();
                info!("Aggregate proof {:?} sectors takes {:?}, result is {:?}", num_proofs_to_aggregate, start.elapsed(), res);


            } else {
                warn!("Commit 1 is error, can't do commit phase2");
            }


            info!("Commit phase 2 takes {:?}", phase2_start.elapsed());

            info!("seal_commit:end");
            SEAL_COMMIT_NUM.fetch_add(1, Ordering::SeqCst);
            info!("##########################");
            info!("##########################");
            info!("Seal commit {:?} sectors!", SEAL_COMMIT_NUM.load(Ordering::SeqCst));
            info!("##########################");
            info!("##########################");




            if get_post_ornot_env() {
                info!("!!!!!!!!!!!Start Window POST!!!!!!!!!!!!!!!");

                let RANDOMNESS: [u8; 32] = [44; 32];

                let comm_r = meta.pre_commit.comm_r;
                let pub_replica = PublicReplicaInfo::new(comm_r).unwrap();
                let priv_replica = PrivateReplicaInfo::<Tree>::new(
                    Path::new(&get_sealed_path(*sector_id).clone()).into(),
                    comm_r,
                    cache_path.clone(),
                ).unwrap();
                let mut pub_replica_info: BTreeMap<SectorId, PublicReplicaInfo> = BTreeMap::new();
                let mut priv_replica_info: BTreeMap<SectorId, PrivateReplicaInfo<Tree>> = BTreeMap::new();
                pub_replica_info.insert(SectorId::from(*sector_id), pub_replica.clone());
                pub_replica_info.insert(SectorId::from(2), pub_replica.clone());
                pub_replica_info.insert(SectorId::from(3), pub_replica.clone());
                pub_replica_info.insert(SectorId::from(4), pub_replica.clone());

                priv_replica_info.insert(SectorId::from(*sector_id), priv_replica.clone());
                priv_replica_info.insert(SectorId::from(2), priv_replica.clone());
                priv_replica_info.insert(SectorId::from(3), priv_replica.clone());
                priv_replica_info.insert(SectorId::from(4), priv_replica.clone());

                let proof = generate_window_post::<Tree>(&(*WINDOW_POST_CONFIG), &RANDOMNESS, &priv_replica_info, prover_id).unwrap();

                let verify_result = verify_window_post::<Tree>(
                    &(*WINDOW_POST_CONFIG),
                    &RANDOMNESS,
                    &pub_replica_info,
                    prover_id,
                    &proof,
                ).unwrap();

                println!("verify_window_post result: {:?}", verify_result);

                for _ in (0..1) {
                    info!("!!!!!!!!!!!Start Winning POST!!!!!!!!!!!!!!!");
                    let pub_replica = PublicReplicaInfo::new(comm_r).unwrap();
                    let priv_replica = PrivateReplicaInfo::<Tree>::new(
                        Path::new(&get_sealed_path(*sector_id).clone()).into(),
                        comm_r,
                        cache_path.clone(),
                    ).unwrap();

                    let pub_replica_info = vec![(SectorId::from(*sector_id), pub_replica)];
                    let priv_replica_info = vec![(SectorId::from(*sector_id), priv_replica)];

                    let challenge = generate_winning_post_sector_challenge::<Tree>(
                        &(*WINNING_POST_CONFIG),
                        &RANDOMNESS,
                        WINNING_POST_SECTOR_COUNT as u64,
                        prover_id,
                    ).unwrap();

                    let proof = generate_winning_post::<Tree>(&(*WINNING_POST_CONFIG), &RANDOMNESS, &priv_replica_info[..], prover_id).unwrap();

                    let verify_result = verify_winning_post::<Tree>(
                        &(*WINNING_POST_CONFIG),
                        &RANDOMNESS,
                        &pub_replica_info[..],
                        prover_id,
                        &proof,
                    ).unwrap();
                    println!("verify_winning_post challenge is {:?} result: {:?}", challenge, verify_result);
                }
            }

        }
        println!("Finish sector {:?} commit @{:?}", sector_id, Instant::now());
        let mut replicas = BTreeMap::new();
        replicas.insert(SectorId::from(*sector_id), PrivateReplicaInfo::<Tree>::new(Path::new(&get_sealed_path(*sector_id)).into()
                                                                                    , meta.pre_commit.comm_r, cache_path).unwrap());
        clear_caches(&replicas);
        set_last_sector_id(sector_id);
        //let out_path = get_sealed_path(*sector_id);
        // (*PRIVATER_EPLICA_INFO).write().unwrap().insert(
        //     SectorId::from(*sector_id),
        //     PrivateReplicaInfo::new(Path::new(&get_sealed_path(*sector_id)).into()
        //                             , meta.pre_commit.comm_r, cache_path).unwrap(),
        // );


    }

}

pub fn winning<Tree: 'static + MerkleTreeTrait>() {
    if &(*REPLICA_INFO_FIELDS_MAP).read().unwrap().len() == &0 {
        info!("No sector has been proved yet, don't do post");
    } else {
        let prover_id: ProverId = [0u8; 32];

        let sector_ids: Vec<u64> =  (*REPLICA_INFO_FIELDS_MAP).read().unwrap().iter().map(|(sector_id, _)| {
            sector_id.clone()
        }).collect();

        let sector_id = sector_ids.choose(&mut rand::thread_rng()).unwrap();
        let proving_set = (*REPLICA_INFO_FIELDS_MAP).read().unwrap();

        let info_fields = proving_set.get(sector_id).unwrap();

        let pub_replica = PublicReplicaInfo::new(info_fields.comm_r.clone()).unwrap();
        let priv_replica = PrivateReplicaInfo::<Tree>::new(
            info_fields.replica.clone(),
            info_fields.comm_r.clone(),
            info_fields.cache_dir.clone(),
        ).unwrap();

        let rng = &mut rand::thread_rng();
        let mut randomness: Ticket = rng.gen();
        rng.fill(&mut randomness[..]);
        randomness[31] &= 0b0011_1111;

        let pub_replica_info = vec![(SectorId::from(*sector_id), pub_replica)];
        let priv_replica_info = vec![(SectorId::from(*sector_id), priv_replica)];

        let challenge = generate_winning_post_sector_challenge::<Tree>(
            &(*WINNING_POST_CONFIG),
            &randomness,
            WINNING_POST_SECTOR_COUNT as u64,
            prover_id,
        ).unwrap();

        let proof = generate_winning_post::<Tree>(&(*WINNING_POST_CONFIG), &randomness, &priv_replica_info[..], prover_id).unwrap();

        let verify_result = verify_winning_post::<Tree>(
            &(*WINNING_POST_CONFIG),
            &randomness,
            &pub_replica_info[..],
            prover_id,
            &proof,
        ).unwrap();
        println!("verify_winning_post challenge is {:?} result: {:?}", challenge, verify_result);
        //     info!("!!!!!!!!!!!!!POST is started!!!!!!!!!!!!");
        //     let start_candidate = Instant::now();
        //     let rng = &mut rand::thread_rng();
        //     let mut randomness=[0u8; 32];
        //     rng.fill(&mut randomness[..]);
        //     randomness[31] &= 0b0000_0000;
        //     info!("Randomess for post is: {:?}", randomness);
        //     //let challenge_count : u64 =  ((&(*PRIVATER_EPLICA_INFO).read().unwrap().len()-1)/25+1) as u64;
        //     let challenge_count : u64 =  ((&(*PRIVATER_EPLICA_INFO).read().unwrap().len()-1)/25+1) as u64;
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
    }


}

pub enum PrecommitPhase1Input {
    precommit_phase1(),
    Shutdown,
}

pub enum PrecommitPhase2Input {
    precommit_phase2(),
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

pub struct PrecommitPhase1Worker {
    pub id: usize,
    pub thread: Option<thread::JoinHandle<()>>,
}

pub struct PrecommitPhase2Worker {
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

impl PrecommitPhase1Worker {
    pub fn start(
        id: usize,
        precommit_phase1_task_rx: Arc<Mutex<mpsc::Receiver<PrecommitPhase1Input>>>,
    ) -> PrecommitPhase1Worker
    {
        let thread = thread::spawn(move || loop {

            let task = {
                let rx = precommit_phase1_task_rx.lock().expect(FATAL_NOLOCK);
                rx.recv().expect(FATAL_RCVTSK)
            };

            // Dispatch to the appropriate task-handler.
            match task {
                PrecommitPhase1Input::precommit_phase1() => {
                    let sector_size = get_data_size();
                    with_shape!(sector_size, precommit_phase1);
                }

                PrecommitPhase1Input::Shutdown => break,
            }
        });

        PrecommitPhase1Worker {
            id,
            thread: Some(thread),
        }
    }
}

impl PrecommitPhase2Worker {
    pub fn start(
        id: usize,
        precommit_phase2_task_rx: Arc<Mutex<mpsc::Receiver<PrecommitPhase2Input>>>,
    ) -> PrecommitPhase2Worker
    {
        let thread = thread::spawn(move || loop {

            let task = {
                let rx = precommit_phase2_task_rx.lock().expect(FATAL_NOLOCK);
                rx.recv().expect(FATAL_RCVTSK)
            };

            // Dispatch to the appropriate task-handler.
            match task {
                PrecommitPhase2Input::precommit_phase2() => {
                    let sector_size = get_data_size();
                    with_shape!(sector_size, precommit_phase2);
                }

                PrecommitPhase2Input::Shutdown => break,
            }
        });

        PrecommitPhase2Worker {
            id,
            thread: Some(thread),
        }
    }
}

impl ProveWorker {
    pub fn start(
        id: usize,
        prove_task_rx: Arc<Mutex<mpsc::Receiver<ProveInput>>>,
        do_bellman: bool,
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
                    with_shape!(sector_size, seal_commit, do_bellman);
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
                    with_shape!(sector_size, winning);
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

pub fn start_precommit_phase1(precommit_phase1_num_worker: usize, precommit_phase1_interval: usize, total_task_num: usize, waiting_num: usize)
{
    let (precommit_phrase1_tx, precommit_phrase1_workers) = {
        let (tx, rx) = mpsc::channel();
        let rx = Arc::new(Mutex::new(rx));

        let workers: Vec<PrecommitPhase1Worker> = (0..precommit_phase1_num_worker)
            .map(|n| {
                PrecommitPhase1Worker::start(
                    n as usize,
                    rx.clone(),
                )
            })
            .collect();

        (tx, workers)
    };
    let mut count = 0;
    loop {
        if count < total_task_num && (*SECTORS_FOR_PROVE).read().unwrap().len()+(*SECTORS_FOR_HASH).read().unwrap().len()<=waiting_num {
            let t = PrecommitPhase1Input::precommit_phase1();
            precommit_phrase1_tx.clone().send(t).expect("Seal send error");
            count = count+1;
        }
        sleep_ms((precommit_phase1_interval*1000) as u32);
    }

}

pub fn start_precommit_phase2(precommit_phase2_num_worker: usize, precommit_phase2_interval: usize)
{
    let (precommit_phrase2_tx, precommit_phrase2_workers) = {
        let (tx, rx) = mpsc::channel();
        let rx = Arc::new(Mutex::new(rx));

        let workers: Vec<PrecommitPhase2Worker> = (0..precommit_phase2_num_worker)
            .map(|n| {
                PrecommitPhase2Worker::start(
                    n as usize,
                    rx.clone(),
                )
            })
            .collect();

        (tx, workers)
    };
    let mut count = 0;
    loop {
        let t = PrecommitPhase2Input::precommit_phase2();
        precommit_phrase2_tx.clone().send(t).expect("Seal send error");
        sleep_ms((precommit_phase2_interval*60000) as u32);
    }

}

pub fn start_prove(prove_num_worker: usize, prove_interval: usize, do_bellman: bool)
{
    let (prove_tx, prove_workers) = {
        let (tx, rx) = mpsc::channel();
        let rx = Arc::new(Mutex::new(rx));

        let workers: Vec<ProveWorker> = (0..prove_num_worker)
            .map(|n| {
                ProveWorker::start(
                    n as usize,
                    rx.clone(),
                    do_bellman
                )
            })
            .collect();

        (tx, workers)
    };
    let start = Instant::now();

    loop {
        let t = ProveInput::commit();
        prove_tx.clone().send(t).expect("Seal send error");
        sleep_ms((prove_interval*1000) as u32);
    }
}

pub fn start_post(post_interval: usize)
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

        let t = PostInput::post();
        post_tx.clone().send(t).expect("Post send error");


        sleep_ms((post_interval*1000) as u32);
    }
}


fn main() {
    fil_logger::init();

    let precommit_phase1_num_worker: usize = get_numeric_env("PRECOMMIT_PHASE1_COUNT".to_string(), 1);
    info!("PRECOMMIT_VDE_COUNT is {:?}", precommit_phase1_num_worker);
    let precommit_phase2_num_worker: usize = get_numeric_env("PRECOMMIT_PHASE2_COUNT".to_string(), 1);
    info!("PRECOMMIT_HASH_COUNT is {:?}", precommit_phase2_num_worker);
    let prove_num_worker: usize = get_numeric_env("COMMIT_COUNT".to_string(), 1);
    info!("COMMIT_COUNT is {:?}", prove_num_worker);
    let total_task_num: usize = get_numeric_env("TOTAL_TASKS".to_string(), 1);
    info!("TOTAL_TASKS is {:?}", total_task_num);
    let precommit_phase1_interval: usize = get_numeric_env("PRECOMMIT_PHASE1_INTERVAL".to_string(), 20);
    info!("PRECOMMIT_PHASE1_INTERVAL is {:?}", precommit_phase1_interval);
    let precommit_phase2_interval: usize = get_numeric_env("PRECOMMIT_PHASE2_INTERVAL".to_string(), 1);
    info!("PRECOMMIT_PHASE2_INTERVAL is {:?}", precommit_phase2_interval);
    let prove_interval: usize = get_numeric_env("COMMIT_INTERVAL".to_string(), 1);
    info!("COMMIT_INTERVAL is {:?}", prove_interval);
    let test_wiining = get_post_ornot_env();
    info!("test winning post is {:?}", test_wiining);
    let do_bellman = get_bellman_ornot_env();
    info!("DO_BELLMAN is {:?}", do_bellman);

    let post_interval: usize = get_numeric_env("POST_INTERVAL".to_string(), 60);
    info!("POST_INTERVAL is {:?}", post_interval);

    let waiting_count: usize = get_numeric_env("WAITING_COUNT".to_string(), precommit_phase1_num_worker*2);
    info!("WAITING_COUNT set for waiting for HASH count is {:?}", waiting_count);

    let restart = get_restart_ornot_env();
    info!("restart mode is {:?}", restart);

    let staging_folder = get_staging_folder();
    if !restart {
        remove_dir_all(staging_folder.clone());
        create_dir_all(staging_folder.clone());
        create_staging_file();
    }

    let staging_folder = get_staging_folder();
    if !restart {
        remove_dir_all(staging_folder.clone());
        create_dir_all(staging_folder.clone());
        create_staging_file();
    }else {
        if !Path::new(&staging_folder).exists(){
            create_dir_all(staging_folder.clone());
        }
        create_staging_file();
    }

    let sealed_folder = get_sealed_folder();
    if !restart {
        remove_dir_all(sealed_folder.clone());
        create_dir_all(sealed_folder.clone());
    }else {
        if !Path::new(&sealed_folder).exists(){
            create_dir_all(sealed_folder.clone());
        }
    }

    let cache_folder = get_cache_folder();
    if !restart {
        let result = remove_dir_all(cache_folder.clone());
        info!("remove dir {:?}, result: {:?}", &cache_folder, result);
        create_dir_all(cache_folder.clone());
    }else {
        if !Path::new(&cache_folder).exists(){
            create_dir_all(cache_folder.clone());
        }
    }

    if restart {
        let last_sector_id = get_last_sector_id() + 1;
        SECTOR_SEQ.store(last_sector_id as u64, Ordering::SeqCst);
    }

    let _ = (*POREP_CONFIG).clone();
    //let _ = (*POST_CONFIG).clone();
    //seal_pre_commit();
    let _ = crossbeam::thread::scope(|s| {
        println!("Start super seal @{:?}", Instant::now());
        info!("Start seal thread pool");
        let precommit_phase1_handler = s.spawn(|_| {
            start_precommit_phase1(precommit_phase1_num_worker.clone(), precommit_phase1_interval.clone(), total_task_num.clone(), waiting_count);
        });
        let precommit_phase2_handler = s.spawn(|_| {
            start_precommit_phase2(precommit_phase2_num_worker.clone(), precommit_phase2_interval.clone());
        });

        info!("Start prove thread pool");
        let commit_handler = s.spawn(|_| {
            start_prove(prove_num_worker, prove_interval, do_bellman);
        });

        if test_wiining {
            info!("Start post thread pool");
            let _ = s.spawn(|_| {
                start_post(post_interval);
            });
        }

        info!("Finished start prove function");
        let _ = precommit_phase1_handler.join().unwrap();
        let _ = precommit_phase2_handler.join().unwrap();
        let _ = commit_handler.join().unwrap();
        // let _ = post_handler.join().unwrap();

    });
}