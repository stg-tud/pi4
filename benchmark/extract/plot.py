import argparse
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.ticker as plticker
import numpy as np

parser = argparse.ArgumentParser(description='Plot benchmark results')
parser.add_argument('filename')
args = parser.parse_args()

df = pd.read_csv(args.filename, delimiter=';', header=0).filter(items=['MAXLEN', 'TIME'])
df['TIME'] = df['TIME'].div(1000)
group = df.groupby('MAXLEN').agg(['min', 'mean', 'max', 'std'])

fig, axes = plt.subplots(3)

group.loc[:,('TIME', 'mean')].plot(title='Type checking time (average of 5 runs)', style='.-', ax=axes[0])
axes[0].xaxis.set_major_locator(plticker.MultipleLocator(5.0))
axes[0].grid(axis='y')
axes[0].set_ylim(ymin=0)
axes[0].set_xlabel('maxlen')
axes[0].set_ylabel('time (s)')

group.loc[:,('TIME', 'mean')].plot(title='Type checking time capped at 120s', style='.-', ax=axes[1])
axes[1].xaxis.set_major_locator(plticker.MultipleLocator(5.0))
axes[1].yaxis.set_major_locator(plticker.MultipleLocator(10.0))
axes[1].grid(axis='y')
axes[1].set_ylim(ymin=0,ymax=120)
axes[1].set_xlabel('maxlen')
axes[1].set_ylabel('time (s)')

group.loc[:,('TIME', 'std')].plot(title='Standard deviation', style='.-', ax=axes[2])
axes[2].set_xlabel('maxlen')
axes[2].set_ylabel('standard deviation (s)')

# m = group.loc[:,('TIME', ['min', 'mean'])]
# plt.fill_between(x=group.index,y1=group.loc[:,('TIME', 'min')].values,y2=group.loc[:,('TIME', 'mean')].values,alpha=0.2)
# plt.fill_between(x=group.index,y1=group.loc[:,('TIME', 'mean')].values,y2=group.loc[:,('TIME', 'max')].values,alpha=0.2)
plt.subplots_adjust(hspace = 0.45)
plt.show()
