use crate::zq::{add::AddMod, mul::MulMod, range_check, sub::SubMod};

#[derive(Clone, Debug)]
pub struct MergeNTT<E: stwo_constraint_framework::EvalAtRow>(pub Vec<Merge<E>>);

#[derive(Clone, Debug)]
pub struct Merge<E: stwo_constraint_framework::EvalAtRow> {
    /// Intermediate result: f1 multiplied by the appropriate root of unity with modular arithmetic components
    pub root_times_f1: MulMod<E>,
    /// Merge butterfly result: f0 + root * f1 with modular arithmetic components
    pub f0_plus_root_times_f1: AddMod<E>,
    /// Merge butterfly result: f0 - root * f1 with modular arithmetic components
    pub f0_minus_root_times_f1: SubMod<E>,
}
impl<E: stwo_constraint_framework::EvalAtRow> Merge<E> {
    pub fn new(
        root_times_f1: MulMod<E>,
        f0_plus_root_times_f1: AddMod<E>,
        f0_minus_root_times_f1: SubMod<E>,
    ) -> Self {
        Self {
            root_times_f1,
            f0_plus_root_times_f1,
            f0_minus_root_times_f1,
        }
    }
}
impl<E: stwo_constraint_framework::EvalAtRow> Default for MergeNTT<E> {
    fn default() -> Self {
        Self(vec![])
    }
}

impl<E: stwo_constraint_framework::EvalAtRow> MergeNTT<E> {
    /// Evaluates merge operations for NTT polynomial combination.
    ///
    /// This function performs the merge operations that combine NTT results from smaller
    /// subproblems into larger polynomial evaluations. The merge process uses roots of unity
    /// to properly combine coefficients from different levels of the NTT tree.
    ///
    /// # Arguments
    ///
    /// * `lookup_elements` - Lookup table elements for modular arithmetic operations.
    /// * `eval` - Evaluation context for constraint framework operations.
    #[allow(clippy::type_complexity)]
    pub fn evaluate(
        self,
        lookup_elements: &range_check::LookupElements,
        eval: &mut E,
    ) -> Vec<E::F> {
        // Perform merge butterfly operations on each pair of coefficients
        let mut result = vec![];
        for merge in self.0.into_iter() {
            // Step 1: Compute f1 * root[i] using modular multiplication
            // where root[i] is the i-th root of unity for this merge level
            MulMod::evaluate(merge.root_times_f1, lookup_elements, eval);

            result.push(merge.f0_plus_root_times_f1.r.clone());
            // Step 2a: Merge butterfly operation - compute f_ntt[2*i] = (f0 + root[i]*f1) % q
            AddMod::evaluate(merge.f0_plus_root_times_f1, lookup_elements, eval);

            // Step 2b: Merge butterfly operation - compute f_ntt[2*i+1] = (f0 - root[i]*f1) % q
            result.push(merge.f0_minus_root_times_f1.r.clone());
            SubMod::evaluate(merge.f0_minus_root_times_f1, lookup_elements, eval);
        }
        result
    }

    pub fn push(&mut self, merge: Merge<E>) {
        self.0.push(merge);
    }
}
