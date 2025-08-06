use crate::zq::{add::AddMod, mul::MulMod, range_check, sub::SubMod};

#[derive(Clone, Debug)]
pub struct SplitNTT<E: stwo_constraint_framework::EvalAtRow>(pub Vec<Split<E>>);

#[derive(Clone, Debug)]
pub struct Split<E: stwo_constraint_framework::EvalAtRow> {
    /// Intermediate result: f1 multiplied by the appropriate root of unity with modular arithmetic components
    pub f_even_plus_f_odd: AddMod<E>,
    pub i2_times_f_even_plus_f_odd: MulMod<E>,
    /// Split butterfly result: f0 + root * f1 with modular arithmetic components
    pub f_even_minus_f_odd: SubMod<E>,
    pub i2_times_f_even_minus_f_odd: MulMod<E>,
    pub i2_times_f_even_minus_f_odd_times_root_inv: MulMod<E>,
}
impl<E: stwo_constraint_framework::EvalAtRow> Split<E> {
    pub fn new(
        f_even_plus_f_odd: AddMod<E>,
        i2_times_f_even_plus_f_odd: MulMod<E>,
        f_even_minus_f_odd: SubMod<E>,
        i2_times_f_even_minus_f_odd: MulMod<E>,
        i2_times_f_even_minus_f_odd_times_root_inv: MulMod<E>,
    ) -> Self {
        Self {
            f_even_plus_f_odd,
            i2_times_f_even_plus_f_odd,
            f_even_minus_f_odd,
            i2_times_f_even_minus_f_odd,
            i2_times_f_even_minus_f_odd_times_root_inv,
        }
    }
}
impl<E: stwo_constraint_framework::EvalAtRow> Default for SplitNTT<E> {
    fn default() -> Self {
        Self(vec![])
    }
}

impl<E: stwo_constraint_framework::EvalAtRow> SplitNTT<E> {
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
    ) -> (Vec<E::F>, Vec<E::F>) {
        // Perform merge butterfly operations on each pair of coefficients
        let mut f0 = vec![];
        let mut f1 = vec![];
        for merge in self.0.into_iter() {
            AddMod::evaluate(merge.f_even_plus_f_odd, lookup_elements, eval);
            f0.push(merge.i2_times_f_even_plus_f_odd.r.clone());
            MulMod::evaluate(merge.i2_times_f_even_plus_f_odd, lookup_elements, eval);

            SubMod::evaluate(merge.f_even_minus_f_odd, lookup_elements, eval);
            MulMod::evaluate(merge.i2_times_f_even_minus_f_odd, lookup_elements, eval);
            f1.push(merge.i2_times_f_even_minus_f_odd_times_root_inv.r.clone());
            MulMod::evaluate(
                merge.i2_times_f_even_minus_f_odd_times_root_inv,
                lookup_elements,
                eval,
            );
        }
        (f0, f1)
    }

    pub fn push(&mut self, merge: Split<E>) {
        self.0.push(merge);
    }
}
