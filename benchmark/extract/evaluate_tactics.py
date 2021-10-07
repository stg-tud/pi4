import argparse
import os
from os import listdir

import matplotlib.pyplot as plt
import matplotlib.ticker as plticker
import pandas as pd
from matplotlib.backends.backend_pdf import PdfPages


def read_and_aggregate(file):
    df = pd.read_csv(file, delimiter=';', header=0).filter(
        items=['MAXLEN', 'TIME'])
    df['TIME'] = df['TIME'].div(1000)
    return df.groupby('MAXLEN').agg(['min', 'mean', 'max', 'std'])


parser = argparse.ArgumentParser(
    description='Visualize performance of different SMT tactics')
parser.add_argument('input_path', type=str)
args = parser.parse_args()

filepaths = [f for f in listdir(args.input_path) if f.endswith(".csv")]
dfs = [(os.path.splitext(f)[0], read_and_aggregate(
    os.path.join(args.input_path, f))) for f in filepaths]

keys = [df[0] for df in dfs]
data = [df[1] for df in dfs]

with PdfPages('results.pdf') as pdf:
  for i, df in enumerate(data):
      fig = plt.figure(i)
      ax = df.loc[:, ('TIME', 'mean')].plot(style='.-')
      ax.xaxis.set_major_locator(plticker.MultipleLocator(5.0))
      ax.legend([keys[i]])
      pdf.savefig()
