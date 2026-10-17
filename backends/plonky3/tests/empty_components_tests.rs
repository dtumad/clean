extern crate alloc;

mod common;

use clean_backend::witness_generation::{
    self, HintTable, Interaction, Mode, Padding, Program, WitnessData, WitnessField,
};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec, GeneratedEnsemble,
};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

/// Distinct AIRs on either side of an empty slot expose accidental index compression.
#[derive(Clone)]
struct Sparse<const EMPTY_FIXED: bool = false>;

impl<const EMPTY_FIXED: bool> GeneratedAirSpec for Sparse<EMPTY_FIXED> {
    const FIELD_ORDER: u64 = 2013265921;
    const PUBLIC_VALUES: usize = 3;
    const WIDTHS: &'static [usize] = &[1, 1, 1];
    const FIXED_WIDTHS: &'static [usize] = &[if EMPTY_FIXED { 1 } else { 0 }, 0, 0];
    const FIXED_HEIGHTS: &'static [usize] = &[0, 0, 0];
    const INTERACTIONS_PER_ROW: &'static [usize] = &[1, 1, 1];
    const VERIFIER_INTERACTIONS: usize = 3;

    fn fixed_row<F: WitnessField>(_: usize, _: u64) -> Vec<F> {
        vec![]
    }

    fn constraints<E: PrimeCharacteristicRing + Clone>(component: usize, row: &[E]) -> Vec<E> {
        vec![row[0].clone() - E::from_usize(component + 1)]
    }

    fn interactions<E: PrimeCharacteristicRing + Clone>(
        component: usize,
        _: &[E],
    ) -> Vec<Interaction<E>> {
        vec![Interaction {
            channel: "rows",
            multiplicity: E::ONE,
            message: vec![E::from_usize(component)],
            assume_guarantees: false,
        }]
    }

    fn verifier_interactions<F: WitnessField>(public: &[F]) -> Vec<Interaction<F>> {
        public
            .iter()
            .enumerate()
            .map(|(component, count)| Interaction {
                channel: "rows",
                multiplicity: -*count,
                message: vec![F::from_usize(component)],
                assume_guarantees: true,
            })
            .collect()
    }
}

impl<F: WitnessField> Program<F> for Sparse {
    const FIELD_ORDER: u64 = <Self as GeneratedAirSpec>::FIELD_ORDER;
    const FUEL: usize = 8;
    const COMPONENTS: usize = 3;
    const PUBLIC_INPUTS: usize = 3;
    const PROVER_INPUTS: usize = 0;
    const HINT_TABLES: &'static [HintTable] = &[];
    const FIXED_WIDTHS: &'static [usize] = &[0, 0, 0];
    const ROW_WIDTHS: &'static [usize] = &[1, 1, 1];
    const COMPONENT_NAMES: &'static [&'static str] = &["first", "unused", "last"];

    fn modes() -> Vec<Mode<F>> {
        [8, 0, 16]
            .into_iter()
            .map(|rows| Mode::Preallocated {
                rows,
                handlers: vec![],
            })
            .collect()
    }

    fn padding() -> Vec<Padding<F>> {
        (0..3)
            .map(|component| Padding {
                input: vec![F::from_usize(component + 1)],
                minimum_rows: 0,
            })
            .collect()
    }

    fn initial_row(component: usize, _: u64, _: &WitnessData<F>) -> Vec<F> {
        vec![F::from_usize(component + 1)]
    }

    fn complete_row(
        _: usize,
        input: &[F],
        _: &WitnessData<F>,
        _: &WitnessData<F>,
    ) -> Result<Vec<F>, String> {
        Ok(input.to_vec())
    }

    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>> {
        <Self as GeneratedAirSpec>::interactions(component, row)
    }

    fn verifier_interactions(public: &[F]) -> Vec<Interaction<F>> {
        <Self as GeneratedAirSpec>::verifier_interactions(public)
    }
}

#[test]
fn empty_middle_component_preserves_generation_and_proof_indices() {
    let public = [8, 0, 16].map(BabyBear::from_u64);
    let witness = witness_generation::generate::<BabyBear, Sparse>(&public, &[]).unwrap();
    let mut extra_slot = witness.clone();
    extra_slot.tables.push(vec![]);
    assert!(extra_slot.into_traces().is_err());
    let mut missing_slot = witness.clone();
    missing_slot.tables.remove(1);
    assert!(missing_slot.into_traces().is_err());
    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        [8, 0, 16]
    );
    let traces = witness.into_traces().unwrap();
    assert_eq!(
        traces.iter().map(Matrix::width).collect::<Vec<_>>(),
        [1, 1, 1]
    );
    assert_eq!(
        traces.iter().map(Matrix::height).collect::<Vec<_>>(),
        [8, 0, 16]
    );
    let statement = GeneratedEnsemble::<BabyBear, Sparse>::new(&[8, 0, 16]).unwrap();
    assert_eq!(statement.component_count(), 3);
    assert_eq!(statement.interaction_count(), 27);
    let config = setup::test_config(19);
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();

    // An omitted table cannot satisfy a verifier demand, including a channel key
    // absent from all the active AIRs.
    let wrong_public = [8, 1, 16].map(BabyBear::from_u64);
    assert!(verify_ensemble(&config, &statement, &proof, &wrong_public).is_err());
    assert!(witness_generation::generate::<BabyBear, Sparse>(&wrong_public, &[]).is_err());

    let wrong_statement = GeneratedEnsemble::<BabyBear, Sparse>::new(&[8, 0, 0]).unwrap();
    assert!(matches!(
        prove_ensemble(&config, &wrong_statement, traces.clone(), &public),
        Err(EnsembleShapeError::StatementTraceHeight {
            component: 2,
            expected: 0,
            actual: 16
        })
    ));
    assert!(verify_ensemble(&config, &wrong_statement, &proof, &public).is_err());
    let mut missing_slot = traces.clone();
    missing_slot.remove(1);
    assert!(matches!(
        prove_ensemble(&config, &statement, missing_slot, &public),
        Err(EnsembleShapeError::TraceCount {
            expected: 3,
            actual: 2
        })
    ));
    let mut reordered = traces;
    reordered.swap(1, 2);
    assert!(matches!(
        prove_ensemble(&config, &statement, reordered, &public),
        Err(EnsembleShapeError::StatementTraceHeight {
            component: 1,
            expected: 0,
            actual: 16
        })
    ));
}

#[test]
fn empty_batch_and_non_power_of_two_heights_are_rejected() {
    for first in [0, 8] {
        assert!(matches!(
            GeneratedEnsemble::<BabyBear, Sparse<true>>::new(&[first, 0, 16]),
            Err(EnsembleShapeError::EmptyFixedTrace { component: 0 })
        ));
    }
    assert!(matches!(
        GeneratedEnsemble::<BabyBear, Sparse>::new(&[0, 0, 0]),
        Err(EnsembleShapeError::NoActiveComponents)
    ));
    assert!(matches!(
        GeneratedEnsemble::<BabyBear, Sparse>::new(&[8, 0, 3]),
        Err(EnsembleShapeError::TraceHeight {
            component: 2,
            height: 3
        })
    ));
}
