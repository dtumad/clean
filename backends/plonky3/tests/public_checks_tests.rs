extern crate alloc;

mod common;

// Fresh upstream output contains helpers unused by these small inventories.
#[allow(
    dead_code,
    unused_imports,
    unused_variables,
    unused_mut,
    unreachable_code
)]
mod isolated {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../.lake/build/public_checks.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_mut)]
mod fibonacci {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../.lake/build/checked_fibonacci.rs"
    ));
}

use clean_backend::witness_generation::{Program, WitnessGenerationError};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleShapeError, EnsembleVerificationError,
};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

fn invalid_checks() -> Vec<Vec<BabyBear>> {
    let mut cases = (0..9)
        .map(|position| {
            let mut values = vec![BabyBear::ZERO; 9];
            values[position] = BabyBear::ONE;
            values
        })
        .collect::<Vec<_>>();
    let mut opposite = vec![BabyBear::ZERO; 9];
    opposite[0] = BabyBear::ONE;
    opposite[1] = -BabyBear::ONE;
    cases.push(opposite);
    cases.push(vec![BabyBear::ONE; 9]);
    cases
}

fn fibonacci_input(checks: &[BabyBear]) -> Vec<BabyBear> {
    [32, 5, 226]
        .into_iter()
        .map(BabyBear::from_u64)
        .chain(checks.iter().copied())
        .collect()
}

#[test]
fn literal_ledger_preserves_every_check_and_zero_occurrence() {
    for checks in core::iter::once(vec![BabyBear::ZERO; 9]).chain(invalid_checks()) {
        let ledger = isolated::PublicChecksProgram::verifier_interactions(&checks);
        assert_eq!(ledger.len(), 18);
        for (pair, value) in ledger.chunks_exact(2).zip(checks) {
            assert_eq!(pair[0].channel, "public-checks");
            assert_eq!(pair[0].message, vec![value]);
            assert_eq!(pair[0].multiplicity, -BabyBear::ONE);
            assert!(pair[0].assume_guarantees);
            assert_eq!(pair[1].channel, "public-checks");
            assert_eq!(pair[1].message, vec![BabyBear::ZERO]);
            assert_eq!(pair[1].multiplicity, BabyBear::ONE);
            assert!(!pair[1].assume_guarantees);
        }
    }
}

#[test]
fn isolated_checks_accept_zero_and_reject_each_violation() {
    let valid = isolated::generate(&[BabyBear::ZERO; 9], &[]).unwrap();
    assert!(valid.tables.is_empty());
    for checks in invalid_checks() {
        assert!(matches!(isolated::generate(&checks, &[]),
            Err(WitnessGenerationError::Runtime(message))
                if message.contains("unhandled channel imbalance") && message.contains("public-checks")));
    }
    // Empty inventories test the scheduler and Lean statement, not the STARK API.
    assert!(matches!(
        isolated::PublicChecksProgramStatement::<BabyBear>::new(&[]),
        Err(EnsembleShapeError::NoComponents)
    ));
}

#[test]
fn public_and_prover_widths_are_checked() {
    assert!(matches!(
        isolated::generate(&[BabyBear::ZERO; 8], &[]),
        Err(WitnessGenerationError::PublicInputWidth {
            expected: 9,
            actual: 8
        })
    ));
    assert!(matches!(
        isolated::generate(&[BabyBear::ZERO; 9], &[BabyBear::ZERO]),
        Err(WitnessGenerationError::ProverInputWidth {
            expected: 0,
            actual: 1
        })
    ));
}

#[test]
fn physical_inventory_and_occurrence_bound_include_public_checks() {
    let input = fibonacci_input(&[BabyBear::ZERO; 9]);
    let traces = fibonacci::generate(&input, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    assert_eq!(heights, vec![32, 32, 256]);
    assert_eq!(
        traces.iter().map(Matrix::width).collect::<Vec<_>>(),
        vec![5, 5, 1]
    );
    let statement = fibonacci::CheckedFibonacciProgramStatement::<BabyBear>::new(&heights).unwrap();
    assert_eq!(statement.component_count(), 3);
    assert_eq!(statement.interaction_count(), 436); // original 418 + 2 × 9
    assert!(matches!(
        fibonacci::CheckedFibonacciProgramStatement::<BabyBear>::new(&[1 << 30, 1, 256]),
        Err(EnsembleShapeError::InteractionCountBound { .. })
    ));
    for checks in invalid_checks() {
        assert!(fibonacci::generate(&fibonacci_input(&checks), &[]).is_err());
    }
}

#[test]
fn proof_verification_rejects_each_public_check_mutation() {
    let config = common::setup::test_config(7);
    let public = fibonacci_input(&[BabyBear::ZERO; 9]);
    let traces = fibonacci::generate(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = fibonacci::CheckedFibonacciProgramStatement::<BabyBear>::new(&heights).unwrap();
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    // Reuse the accepted proof directly; no witness generation runs for these mutations.
    for checks in invalid_checks() {
        let invalid = fibonacci_input(&checks);
        assert!(matches!(
            verify_ensemble(&config, &statement, &proof, &invalid),
            Err(EnsembleVerificationError::Proof(_))
        ));
        // Bypass the witness scheduler and bind the invalid cells into a fresh proof.
        // The physical AIR ignores them; the public-only channel must reject them.
        let (invalid_proof, _) =
            prove_ensemble(&config, &statement, traces.clone(), &invalid).unwrap();
        let error = verify_ensemble(&config, &statement, &invalid_proof, &invalid).unwrap_err();
        assert!(format!("{error:?}").contains("GlobalCumulativeMismatch(Some(\"public-checks\"))"));
    }
}
