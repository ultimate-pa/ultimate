import sys, json, argparse
import matplotlib.pyplot as plt
import matplotlib.ticker as plt_ticker
import matplotlib.colors as plt_colors
import re
import random

# The script uses stdin if it is started without arguments.
# To exit stdin use "ctrl + d".

# Example input json string:
'''
{
  "signal": [
    {"name": "A", "wave": "l..h..x."}
  ],
  "head": {
    "text": "figure title"
  }
}
'''

# Supported colors: https://matplotlib.org/3.1.0/gallery/color/named_colors.html
COLORS = [i for i in plt_colors.TABLEAU_COLORS.keys()]


def parseArguments():
  parser = argparse.ArgumentParser()
  parser.add_argument("-i", "--input", help="input file (default: stdin)", type=str, default="")
  parser.add_argument("-o", "--output", help="output file", type=str, default="")
  args = parser.parse_args()

  # Check file extension.
  extensions = ('ps', 'eps', 'pdf', 'pgf', 'png', 'raw', 'rgba', 'svg', 'svgz', 'jpg', 'jpeg', 'tif', 'tiff')
  if args.output and not args.output.endswith(extensions):
    raise ValueError('Output file must be of type: ' + ', '.join(extensions))

  return args


def parseJson(args):
  with sys.stdin if not args.input else open(args.input) as json_input:
    request = json.load(json_input)

  # TODO: Maybe check the input here. ;-)
  request['signal'].reverse()

  return request


def plotSignal(signal, y_offset):
  color = 'black'
  if 'color' in signal:
    color = random.choice(COLORS) if signal['color'] == 'random' else signal['color']
 
  prev = ''
  for i in range(len(signal['wave'])):
    curr = signal['wave'][i]

    if curr not in ['l', 'h', 'x', '.']:
      print('Unsupported char at pos %d in wave: %s' % (i, signal['wave']))
      continue

    if curr == '.':
      curr = prev if prev else 'x'

    if curr == 'l' or curr == 'x':
      plt.hlines(y_offset - 0.5, i, i + 1, colors=color)

    if curr == 'h' or curr == 'x':
      plt.hlines(y_offset + 0.5, i, i + 1, colors=color)

    if curr == 'x':
      rect = plt.Rectangle((i, y_offset - 0.5), 1, 1, fill=False, hatch='///', linewidth=0, color=color)
      plt.gca().add_patch(rect)

    if prev and prev != curr:
      plt.vlines(i, y_offset - 0.5, y_offset + 0.5, colors=color)

    prev = curr


def main():
  args = parseArguments()
  request = parseJson(args)

  fig, ax = plt.gcf(), plt.gca()
  y_ticks, y_ticklabels = [], []

  for i in range(len(request['signal'])):
    y_offset = 0.5 + 2 * i
    signal = request['signal'][i]
    y_ticklabels.append(signal['name'])
    y_ticks.append(y_offset)

    plotSignal(signal, y_offset)

  # Set figure title.
  # ax.set_title(request['head']['text'])

  # Set figure hight dependent on num signals.
  margins_y = fig.subplotpars.top - fig.subplotpars.bottom
  fig.set_size_inches(fig.get_size_inches()[0], margins_y + len(request['signal']) * 0.6)

  # Set label, tick locators and a grid for x axis.
  ax.xaxis.set_major_locator(plt_ticker.MaxNLocator(integer=True))
  ax.xaxis.set_minor_locator(plt_ticker.MultipleLocator(1.0))
  ax.xaxis.grid(which='both', linestyle='dotted')
  ax.set_xlabel('time (t)')

  # Set ticks, tick labels.
  ax.set_yticks(y_ticks)
  ax.set_yticklabels(y_ticklabels)
  ax.set_ylim(y_ticks[0] -1, y_ticks[-1] + 1)

  plt.tight_layout()
  plt.savefig(args.output) if args.output else plt.show()


if __name__ == "__main__":
  main()
