// relation_macros.rs
#[macro_export]
macro_rules! enum_relation {
    (
      $(#[$meta:meta])*
      $vis:vis enum $name:ident {
          $( $var:ident ( $ty:ty ) ),+ $(,)?
      }
    ) => {
        $(#[$meta])*
        $vis enum $name { $( $var($ty) ),+ }


        impl<F, EF> stwo_constraint_framework::Relation<F, EF> for $name
        where
            F: Clone,
            EF: stwo_constraint_framework::RelationEFTraitBound<F>,
        {
            fn combine(&self, values: &[F]) -> EF {
                match self { $( Self::$var(inner) => inner.combine(values), )+ }
            }
            fn get_name(&self) -> &str {
                match self { $( Self::$var(inner) => < $ty as stwo_constraint_framework::Relation<F, EF> >::get_name(inner), )+ }
            }
            fn get_size(&self) -> usize {
                match self { $( Self::$var(inner) => < $ty as stwo_constraint_framework::Relation<F, EF> >::get_size(inner), )+ }
            }
        }

        $(
            impl From<$ty> for $name {
                fn from(x: $ty) -> Self { Self::$var(x) }
            }
        )+
    }
}
