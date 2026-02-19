#!/usr/bin/env python3

import json
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import re
from pathlib import Path

def parse_benchmark_data(json_file):
    """Parse hyperfine JSON output and organize by backend and benchmark."""
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    # Parse each result
    parsed_results = []
    for result in data['results']:
        backend = result['parameters']['backend']
        bench_param = result['parameters']['bench']
        
        # Extract benchmark name and argument
        # bench_param looks like "even 0" or "unionfind 100000"
        parts = bench_param.split()
        bench_name = parts[0]
        bench_arg = int(parts[1]) if len(parts) > 1 else 0
        
        parsed_results.append({
            'backend': backend,
            'bench_name': bench_name,
            'bench_arg': bench_arg,
            'median_time': result['median'],
            'stddev': result['stddev'],
            'command': result['command']
        })
    
    return pd.DataFrame(parsed_results)

def compute_baseline_adjusted_times(df):
    """Subtract baseline (arg=0) times from corresponding non-zero runs."""
    adjusted_results = []
    
    # Group by backend and benchmark name
    for (backend, bench_name), group in df.groupby(['backend', 'bench_name']):
        # Find baseline (arg=0) and non-zero runs
        baseline_runs = group[group['bench_arg'] == 0]
        nonzero_runs = group[group['bench_arg'] != 0]
        
        if len(baseline_runs) == 0:
            print(f"Warning: No baseline (arg=0) found for {backend}/{bench_name}")
            # Use the runs as-is if no baseline
            for _, row in nonzero_runs.iterrows():
                adjusted_results.append({
                    'backend': backend,
                    'bench_name': bench_name,
                    'bench_arg': row['bench_arg'],
                    'adjusted_time': row['median_time'],
                    'raw_time': row['median_time']
                })
            continue
        
        if len(baseline_runs) > 1:
            print(f"Warning: Multiple baselines found for {backend}/{bench_name}, using first")
        
        baseline_time = baseline_runs.iloc[0]['median_time']
        
        # Subtract baseline from each non-zero run
        for _, row in nonzero_runs.iterrows():
            raw_time = row['median_time']
            adjusted_time = raw_time - baseline_time
            
            # Warn if baseline took longer than the actual benchmark
            if baseline_time > raw_time:
                print(f"WARNING: Baseline ({baseline_time:.6f}s) took LONGER than benchmark run "
                      f"({raw_time:.6f}s) for {backend}/{bench_name} arg={row['bench_arg']}")
                print(f"         This suggests the 'zero' case is not actually a no-op baseline!")
            
            # Clamp negative values to 0 for visualization purposes
            adjusted_time = max(0, adjusted_time)
            
            adjusted_results.append({
                'backend': backend,
                'bench_name': bench_name,
                'bench_arg': row['bench_arg'],
                'adjusted_time': adjusted_time,
                'raw_time': raw_time,
                'baseline_time': baseline_time
            })
    
    return pd.DataFrame(adjusted_results)

def create_visualization(df, reference_backend='malfunction-reference'):
    """Create a heatmap visualization of benchmark results."""
    
    # For simplicity, take the maximum bench_arg for each (backend, bench_name) pair
    # This assumes you want to compare the "big" runs
    summary_df = df.loc[df.groupby(['backend', 'bench_name'])['bench_arg'].idxmax()]
    
    # Pivot to create matrix: rows=benchmarks, cols=backends
    matrix_df = summary_df.pivot(index='bench_name', columns='backend', values='adjusted_time')
    
    # Reorder columns: lean first, malfunction-reference second, then alphabetical
    columns = list(matrix_df.columns)
    ordered_columns = []
    
    if 'lean' in columns:
        ordered_columns.append('lean')
        columns.remove('lean')
    
    if 'malfunction-reference' in columns:
        ordered_columns.append('malfunction-reference')
        columns.remove('malfunction-reference')
    
    # Add remaining columns alphabetically
    ordered_columns.extend(sorted(columns))
    matrix_df = matrix_df[ordered_columns]
    
    # Compute relative performance compared to reference backend
    if reference_backend in matrix_df.columns:
        reference_times = matrix_df[reference_backend]
        # Compute ratio: other_backend_time / reference_time
        relative_matrix = matrix_df.div(reference_times, axis=0)
        title_suffix = f" (relative to {reference_backend})"
        colorbar_label = f"Time ratio (vs {reference_backend})"
        
        # Handle outliers: identify ratios > 20 or < 1/20
        outlier_mask = (relative_matrix > 20) | (relative_matrix < 1/20)
        relative_matrix_clipped = relative_matrix.copy()
        relative_matrix_clipped[outlier_mask] = np.nan  # Exclude from colorbar calculation
        
    else:
        print(f"Warning: Reference backend '{reference_backend}' not found. Using absolute times.")
        available_backends = list(matrix_df.columns)
        print(f"Available backends: {available_backends}")
        relative_matrix = matrix_df
        relative_matrix_clipped = relative_matrix
        outlier_mask = pd.DataFrame(False, index=relative_matrix.index, columns=relative_matrix.columns)
        title_suffix = " (absolute times)"
        colorbar_label = "Adjusted time (seconds)"
    
    # Create the plot
    fig, ax = plt.subplots(figsize=(12, 8))
    
    # Use a diverging colormap for relative performance (if using ratios)
    if reference_backend in matrix_df.columns:
        # For logarithmic scaling, we need to handle the data transformation
        log_matrix = np.log10(relative_matrix_clipped)  # Use clipped data for colorbar range
        vmin, vmax = log_matrix.min().min(), log_matrix.max().max()
        vcenter = 0  # log10(1) = 0
        # Extend range symmetrically around 0 for better visualization
        vrange = max(abs(vmin - vcenter), abs(vmax - vcenter))
        vmin, vmax = vcenter - vrange, vcenter + vrange
        cmap = 'RdBu_r'  # Red=slow, Blue=fast, colorblind-friendly
        
        # Create plot data with outliers set to NaN, then handle separately
        plot_data = np.log10(relative_matrix).values
        plot_data[outlier_mask.values] = np.nan
        
    else:
        vmin, vmax = None, None
        cmap = 'RdBu_r'
        plot_data = relative_matrix.values
    
    im = ax.imshow(plot_data, cmap=cmap, vmin=vmin, vmax=vmax, aspect='auto')
    
    # Manually color outliers black by overlaying patches
    if reference_backend in matrix_df.columns:
        for i in range(len(relative_matrix.index)):
            for j in range(len(relative_matrix.columns)):
                if outlier_mask.iloc[i, j]:
                    # Add a black rectangle for this cell
                    rect = plt.Rectangle((j-0.5, i-0.5), 1, 1, facecolor='black', edgecolor='none')
                    ax.add_patch(rect)
    
    # Set ticks and labels
    ax.set_xticks(range(len(relative_matrix.columns)))
    ax.set_xticklabels(relative_matrix.columns, rotation=45, ha='right')
    ax.set_yticks(range(len(relative_matrix.index)))
    ax.set_yticklabels(relative_matrix.index)
    
    # Add colorbar with logarithmic ticks if using ratios
    cbar = plt.colorbar(im, ax=ax)
    if reference_backend in matrix_df.columns:
        log_ticks = np.log10([0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
        cbar.set_ticks(log_ticks)
        cbar.set_ticklabels(["0.1", "0.2"] + [""]*7 + ["1", "2"] + [""]*7 + ["10"])
        cbar.set_label(colorbar_label)
    else:
        cbar.set_label(colorbar_label)
    
    # Add text annotations with values
    for i in range(len(relative_matrix.index)):
        for j in range(len(relative_matrix.columns)):
            value = relative_matrix.iloc[i, j]
            is_outlier = outlier_mask.iloc[i, j] if reference_backend in matrix_df.columns else False
            
            if not np.isnan(value):
                if reference_backend in matrix_df.columns:
                    if is_outlier:
                        text = f'{value:.0f}' if value >= 1 else f'{value:.2f}'
                        text_color = 'white'  # White text on black background for outliers
                    else:
                        text = f'{value:.2f}'
                        # For log scale, determine text color based on distance from center (1.0x)
                        log_value = np.log10(value)
                        # Normalize to [0,1] range for color intensity check
                        normalized_pos = (log_value - vmin) / (vmax - vmin) if vmax != vmin else 0.5
                        # Use black text for light colors (middle range), white for dark colors (extremes)
                        text_color = 'white' if normalized_pos < 0.3 or normalized_pos > 0.7 else 'black'
                else:
                    text = f'{value:.3f}'
                    normalized_pos = im.norm(value) if hasattr(im, 'norm') else 0.5
                    text_color = 'white' if normalized_pos < 0.3 or normalized_pos > 0.7 else 'black'
                
                ax.text(j, i, text, ha='center', va='center', 
                       color=text_color, fontsize=8, weight='bold')
    
    ax.set_title(f'Benchmark Performance Comparison{title_suffix}')
    ax.set_xlabel('Backend')
    ax.set_ylabel('Benchmark')
    
    plt.tight_layout()
    return fig

def main():
    import sys
    
    if len(sys.argv) != 2:
        print("Usage: python wide_viz.py <json_file>")
        sys.exit(1)
    
    json_file = sys.argv[1]
    
    if not Path(json_file).exists():
        print(f"Error: File {json_file} not found")
        sys.exit(1)
    
    # Parse and process data
    print("Parsing benchmark data...")
    df = parse_benchmark_data(json_file)
    print(f"Found {len(df)} benchmark results")
    
    print("Computing baseline-adjusted times...")
    adjusted_df = compute_baseline_adjusted_times(df)
    print(f"Generated {len(adjusted_df)} adjusted results")
    
    # Create visualization
    print("Creating visualization...")
    fig = create_visualization(adjusted_df)
    
    # Save and show
    # output_file = "benchmark_comparison.png"
    # fig.savefig(output_file, dpi=300, bbox_inches='tight')
    # print(f"Saved visualization to {output_file}")
    
    plt.show()

if __name__ == "__main__":
    main()
