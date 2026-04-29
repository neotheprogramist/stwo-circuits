macro_rules! define_component_list {
    ($($variant:ident),* $(,)?) => {
        pub enum ComponentList {
            $($variant),*
        }
        pub const N_COMPONENTS: usize = [$(stringify!($variant)),*].len();
    };
}

define_component_list! {
    Eq,
    Qm31Ops,
    PoseidonGate,
    M31ToU32,
    RangeCheck16,
}
