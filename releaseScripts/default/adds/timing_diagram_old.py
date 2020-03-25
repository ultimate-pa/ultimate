import sys, json, argparse
import matplotlib.pyplot as plt
import matplotlib.ticker as plt_ticker
from collections import namedtuple

class TimingDiagram:
  Signal = namedtuple('Signal', 'id x y')

  def __init__(self, filename, title, signals, append_steps):
    self.filename = filename
    self.title = title
    self.signals = signals
    self.append_steps = append_steps
    self.signal_height = 0.8
    self.signal_spacing = 1.0

    # Find max number of steps.
    max_step = 0
    for signal in self.signals:
      max_step = max(max_step, signal.x[-1] + self.append_steps)

    # Insert value at zero and max number steps if needed. 
    for signal in self.signals:
      if signal.x[0] > 0:
        signal.x.insert(0, 0)
        signal.y.insert(0, 0)

      if signal.x[-1] < max_step:
        signal.x.append(max_step)
        signal.y.append(signal.y[-1])

      # Replace dont care with 0.
      for i in range(len(signal.y)):
        signal.y[i] = signal.y[i] if signal.y[i] != -1 else 0

  def plot(self):
    yticks, yticklabels = [], []
    fig, ax = plt.gcf(), plt.gca()

    # Create a step plot, yticks and yticklabels for each signal.
    for i in range(len(self.signals)):
      plt.step(self.signals[i].x, [y + i * 2 for y in self.signals[i].y], where='post')
      yticks.extend([v + i * 2 for v in (0.0, 0.5, 1.0)])
      yticklabels.extend([v for v in ('0', self.signals[i].id + '        ', '1')])

    # Set figure hight dependent on num signals.
    margins_y = fig.subplotpars.top - fig.subplotpars.bottom
    fig.set_size_inches(fig.get_size_inches()[0], margins_y + self.signal_height * len(self.signals))

    # Set figure title.
    ax.set_title(self.title)

    # Set label, tick locators and a grid for x axis.
    ax.set_xlabel('t')
    ax.xaxis.set_major_locator(plt_ticker.MaxNLocator(integer=True))
    ax.xaxis.set_minor_locator(plt_ticker.MultipleLocator(1.0))
    ax.xaxis.grid(which='both', linestyle='dotted')

    # Set ticks, tick labels and limits for y axis.
    ax.set_yticks(yticks)
    ax.set_yticklabels(yticklabels)
    ax.set_ylim(-0.5, 2 * len(self.signals) - 0.5)

    # Hack, to remove tick at signal name. Simulates multiple labels for y axis.
    for tic in ax.yaxis.get_major_ticks()[1::3]:
      tic.tick1line.set_visible(False)
      tic.tick2line.set_visible(False)

    # Save figure if a filename is given, else show it.
    plt.tight_layout()
    plt.savefig(self.filename) if self.filename else plt.show()


def main():
  extensions = ('ps', 'eps', 'pdf', 'pgf', 'png', 'raw', 'rgba', 'svg', 'svgz', 'jpg', 'jpeg', 'tif', 'tiff')

  # Parse command line arguments.
  parser = argparse.ArgumentParser()
  parser.add_argument("-i", "--input", help="input file or stdin (default: stdin)", type=str, default="")
  parser.add_argument("-o", "--output", help="output file", type=str, default="")
  parser.add_argument("-a", "--append_steps", help="number of time steps to append", type=int, default=0)
  args = parser.parse_args()

  # Check file extension.
  if args.output and not args.output.endswith(extensions):
    raise ValueError('Output file must be of type: ' + ', '.join(extensions))

  # Parse json from file or stdin.
  with sys.stdin if not args.input else open(args.input) as json_str:
    request = json.load(json_str)

  signals = [TimingDiagram.Signal(v['id'], v['x'], v['y']) for v in request['signals']]

  # Plot that shit.
  diagram = TimingDiagram(args.output, request['id'], signals, args.append_steps)
  diagram.plot()

if __name__ == "__main__":
  main()
