use frame_support::weights::Weight;

pub struct WeightInfo;
impl pallet_derivatives::WeightInfo for WeightInfo {
	fn create_derivative() -> Weight {
		Weight::from_parts(100_000_000, 0)
	}

	fn destroy_derivative() -> Weight {
		Weight::from_parts(100_000_000, 0)
	}
}
