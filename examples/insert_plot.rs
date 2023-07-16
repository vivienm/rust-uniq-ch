use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash, Hasher},
    path::{Path, PathBuf},
    time::Duration,
};

use clap::Parser;
use plotters::prelude::*;
use uniq_ch::Bjkst;

/// Plot insertion times in a BJKST.
#[derive(Debug, Parser)]
struct Args {
    /// The number of elements to insert.
    #[clap(default_value = "1000000")]
    size: usize,
    #[clap(short, long, default_value = "output.png", value_parser)]
    output: PathBuf,
}

fn draw<P>(durations: &[Duration], output: P) -> anyhow::Result<()>
where
    P: AsRef<Path>,
{
    let drawing_area = BitMapBackend::new(&output, (1024, 768)).into_drawing_area();
    drawing_area.fill(&WHITE)?;

    let mut chart = ChartBuilder::on(&drawing_area)
        .set_label_area_size(LabelAreaPosition::Left, 60)
        .set_label_area_size(LabelAreaPosition::Bottom, 60)
        .caption("Insertion times", ("sans-serif", 40))
        .build_cartesian_2d(
            0..(durations.len() - 1),
            0.0f64..(durations.iter().max().unwrap().as_nanos() as f64),
        )?;

    chart
        .configure_mesh()
        .disable_x_mesh()
        .disable_y_mesh()
        .draw()?;

    chart.draw_series(
        AreaSeries::new(
            durations
                .iter()
                .enumerate()
                .map(|(i, duration)| (i, duration.as_nanos() as f64)),
            0.0,
            &RED.mix(0.2),
        )
        .border_style(&RED),
    )?;

    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let mut durations = Vec::with_capacity(args.size);
    let mut bjkst = Bjkst::<usize>::new();
    let build_hasher = RandomState::new();

    for i in 1..=args.size {
        // Compute the hash value manually, to avoid the overhead of hashing in the
        // benchmark.
        let mut hasher = build_hasher.build_hasher();
        i.hash(&mut hasher);
        let hash = hasher.finish();

        let start = std::time::Instant::now();
        bjkst.insert_hash(hash);
        let end = std::time::Instant::now();

        let duration = end.duration_since(start);
        durations.push(duration);
    }

    draw(&durations, args.output)?;

    println!(
        "Inserted {} elements in {:?}",
        args.size,
        durations.iter().sum::<Duration>()
    );
    println!("Count: {}", bjkst.len());

    Ok(())
}
