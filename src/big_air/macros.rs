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

#[macro_export]
macro_rules! impl_big_ic {
    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis struct $name { $($body)* }

        impl $name {
            #[inline]
            pub fn mix_into(&self, ch: &mut impl stwo::core::channel::Channel) {
                $crate::impl_big_ic!(@mix_fields self ch; $($body)*);
            }

            #[inline]
            pub fn claimed_sum(&self) -> QM31 {
                $crate::impl_big_ic!(@sum_fields self; $($body)*)
            }
        }
    };

    // ---------- mix_into muncher ----------
    // Vec field + trailing comma
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : Vec<$inner:ty>, $($rest:tt)*) => {
        for ic in $self.$field.iter() { ic.mix_into($ch); }
        $crate::impl_big_ic!(@mix_fields $self $ch; $($rest)*);
    };
    // Non-Vec field + trailing comma
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : $ty:ty, $($rest:tt)*) => {
        $self.$field.mix_into($ch);
        $crate::impl_big_ic!(@mix_fields $self $ch; $($rest)*);
    };
    // Vec last field (no trailing comma)
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : Vec<$inner:ty>) => {
        for ic in $self.$field.iter() { ic.mix_into($ch); }
    };
    // Non-Vec last field (no trailing comma)
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : $ty:ty) => {
        $self.$field.mix_into($ch);
    };
    // Empty (safety)
    (@mix_fields $self:ident $ch:ident; ) => {};

    // ---------- claimed_sum muncher ----------
    // Vec field + trailing comma
    (@sum_fields $self:ident; $fvis:vis $field:ident : Vec<$inner:ty>, $($rest:tt)*) => {
        $self.$field.iter().map(|x| x.claimed_sum).sum::<QM31>()
            + $crate::impl_big_ic!(@sum_fields $self; $($rest)*)
    };
    // Non-Vec field + trailing comma
    (@sum_fields $self:ident; $fvis:vis $field:ident : $ty:ty, $($rest:tt)*) => {
        $self.$field.claimed_sum
            + $crate::impl_big_ic!(@sum_fields $self; $($rest)*)
    };
    // Vec last field (no trailing comma)
    (@sum_fields $self:ident; $fvis:vis $field:ident : Vec<$inner:ty>) => {
        $self.$field.iter().map(|x| x.claimed_sum).sum::<QM31>()
    };
    // Non-Vec last field (no trailing comma)
    (@sum_fields $self:ident; $fvis:vis $field:ident : $ty:ty) => {
        $self.$field.claimed_sum
    };
    // Empty (if someone ever uses it on an empty struct)
    (@sum_fields $self:ident; ) => {
        <QM31 as num_traits::Zero>::zero()
    };
}

#[macro_export]
macro_rules! impl_mix_into {
    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis struct $name { $($body)* }

        impl $name {
            #[inline]
            pub fn mix_into(&self, ch: &mut impl stwo::core::channel::Channel) {
                $crate::impl_mix_into!(@mix_fields self ch; $($body)*);
            }
        }
    };

    // ---------- mix_into muncher ----------
    // Vec field + trailing comma
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : Vec<$inner:ty>, $($rest:tt)*) => {
        for ic in $self.$field.iter() { ic.mix_into($ch); }
        $crate::impl_mix_into!(@mix_fields $self $ch; $($rest)*);
    };
    // Non-Vec field + trailing comma
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : $ty:ty, $($rest:tt)*) => {
        $self.$field.mix_into($ch);
        $crate::impl_mix_into!(@mix_fields $self $ch; $($rest)*);
    };
    // Vec last field (no trailing comma)
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : Vec<$inner:ty>) => {
        for ic in $self.$field.iter() { ic.mix_into($ch); }
    };
    // Non-Vec last field (no trailing comma)
    (@mix_fields $self:ident $ch:ident; $fvis:vis $field:ident : $ty:ty) => {
        $self.$field.mix_into($ch);
    };
    // Empty (safety)
    (@mix_fields $self:ident $ch:ident; ) => {};

}
