# Heterogeneous DP-SGD on CIFAR-10

Compare single-threshold and personalized gradient weighting. This package
reproduces six figures: training and test accuracy, two analytical MSE-ratio
curves, and two empirical sweeps over privacy budgets and group sizes.


## Install

Use Python 3.11 or 3.12. Run the following from this directory:

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
```

## Reproduce figures from recorded results

```bash
python reproduce.py
```

Writes six PDFs and PNGs to `figures/`, with filenames matching the paper.
No GPU or CIFAR-10 download is needed. The earlier theoretical heatmaps are
outside this package's scope.

## Reproduce training and figures end to end

An NVIDIA GPU is required. Download and extract the CIFAR-10 Python dataset
so that `/path/to/data/cifar-10-batches-py/data_batch_1` exists, then run:

```bash
python reproduce.py train --cifar /path/to/data --root runs/new
```

This runs 30 trainings for the learning curves and 130 for the sensitivity
sweeps, then generates the figures in `runs/new/figures/`. It uses the paper's
fixed, validation-selected parameters rather than repeating hyperparameter
tuning. The run directory must be new; numerical results can vary with hardware.

On a Slurm cluster, activate the installed environment and adapt resource
directives in `slurm/array.slurm` to your allocation, then run:

```bash
python reproduce.py submit --cifar /path/to/data --root runs/new --parallel 32
```

Plotting runs automatically after successful training. Training never downloads data.

## Rerun validation and parameter selection

```bash
python reproduce.py validate --cifar /path/to/data --root runs/validation
python reproduce.py train --cifar /path/to/data --root runs/retuned --selected runs/validation/selected.json
```

For Slurm, use `validate-submit` instead of `validate`. Wait for
`runs/validation/selected.json`, then use `submit` instead of `train` in the
second command (both accept `--parallel 32`).

Validation uses a fixed 45,000/5,000 train/validation split, both methods, and
three runs per method and candidate: **204 training runs**. No test accuracy
is used. For each profile, selection maximizes mean final validation accuracy
across both methods and the three runs. The selected recipe is shared by the
two methods. `candidates.json` records all scores; `selected.json` records winners.

The tested tuples are **(logical batch size, epochs, initial learning rate)**,
not a Cartesian product:

| Grid | Tested tuples |
|---|---|
| Low | (5000, 30, 0.00625), (5000, 30, 0.01875), (1000, 30, 0.001875), (1000, 30, 0.00625), (1000, 30, 0.01875) |
| High | (5000, 30, 0.01875), (1000, 60, 0.00625), (1000, 60, 0.01875), (1000, 60, 0.04375) |
| Public | (1000, 60, 0.01875), (1000, 60, 0.04375), (1000, 90, 0.04375) |

Low applies to (1, 0.01), (1, 0.1), and the survey profile; High to (4, 1),
(8, 1), (8, 4), and survey x8; Public to public/private (private epsilon 1).
Two-level/public profiles assign 20% of records to the first group and 80%
to the second. The survey profile assigns 54% uniformly on [0.01, 0.2], 37%
uniformly on [0.2, 1], and 9% to 1, rounded to hundredths; x8 scales all budgets.

Fixed settings: clipping norm 16, the GroupNorm CNN, SGD momentum 0.9,
weight decay 0.0005, cosine learning-rate schedule, microbatch size 64,
delta 1e-5, and random crop/flip augmentation. Weights and noise are calibrated
for each candidate's complete training horizon.

The final command uses the new selections for the three main-figure profiles.
The two empirical sensitivity sweeps remain a fixed-recipe study: batch 1000,
30 epochs, initial learning rate 0.00625, clipping norm 16. They are not retuned.

Privacy accounting is per training run and excludes repeated trials and exact
diagnostics. Sweep plots use separately scaled axes with aligned extrema;
connecting lines do not represent additional experiments.

## Pipeline

All commands go through `reproduce.py`. There are two ways to produce the figures:
redraw the recorded results in `data/`, or generate new results by training.

1. **Validate and select (optional).** `experiment.py` defines the candidate
   batch sizes, training horizons, and learning rates listed below. Each
   candidate trains both methods on 45,000 images and evaluates on the same
   5,000 validation images. `reproduce.py` averages final validation accuracy
   across both methods and three runs, then saves the best shared configuration
   for each privacy profile in `selected.json`. Skipping this step uses the
   paper's selections in `data/paper/selected.json`.
2. **Train the comparisons.** `train.py` trains from scratch on all 50,000
   training images with five paired runs per method. The three main profiles
   use the selected configurations (30 runs). Separately,
   `sensitivity_sweep.py` specifies 13 budget/group-size configurations with
   a fixed training recipe (130 runs). Each run writes epochwise train/test
   accuracy to `epochs.csv` and its configuration and privacy audit to
   `summary.json`.
3. **Construct each private update.** Before training, `privacy.py` assigns
   the record budgets. `sampled_privacy.py` calibrates Gaussian noise for the
   sampling rate and full training horizon. It compares feasible thresholds
   or uses `optimal_weights.py` to select personalized weights minimizing
   the sampled MSE bound. During training, `train.py` samples records uniformly,
   clips each record's gradient, forms the weighted sum, adds noise once per
   logical batch, and updates the CNN. Both methods share the learning rate
   and other training settings within each comparison.
4. **Aggregate and plot.** Completed runs are checked for matching configurations,
   complete epochs, and privacy-budget compliance. `reproduce.py` and
   `sensitivity_sweep.py` aggregate accuracies and paired differences with
   pointwise 95% Student-t intervals. `paper_figures.py` draws the train/test
   curves and the analytical ratios computed by `mse_theory.py`;
   `sensitivity_sweep.py` draws the two empirical sweep figures. The six PDFs
   and PNGs are saved under the run's `figures/` directory.

The plotting-only command starts at step 4 using the supplied aggregate
exports, without retraining. Slurm submission uses `slurm/array.slurm` and
automatically runs aggregation after all training jobs succeed.
