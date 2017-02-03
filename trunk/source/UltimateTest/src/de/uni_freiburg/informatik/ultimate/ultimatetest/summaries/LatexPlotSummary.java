/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.summaries;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 *
 * Note: This summary is work in progress and not complete! Do not use it until this message vanishes.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class LatexPlotSummary extends LatexSummary {

	private final int mLatexTableHeaderCount;

	public LatexPlotSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			final ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);
		mLatexTableHeaderCount = (int) mColumnDefinitions.stream().filter(a -> a.getLatexColumnTitle() != null).count();
	}

	@Override
	public String getSummaryLog() {
		final StringBuilder sb = new StringBuilder();
		final PartitionedResults results = partitionResults(mResults.entrySet());
		makeTables(sb, results);
		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}

	private void makeTables(final StringBuilder sb, final PartitionedResults results) {

		final Set<String> tools = CoreUtil.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getToolchain().getName();
			}
		});

		final String br = CoreUtil.getPlatformLineSeparator();

		appendPreamble(sb, br);
		// appendLatexFigureBegin(sb, br);
		// for funName, filesAndNames in latexFigures:
		// sortedByName = sorted(filesAndNames, key=lambda x : x[1])
		// f.write('\\resizebox*{0.45\\textwidth}{!}{%\n')
		// appendLatexFigure(sb, 'x', 'y', sortedByName, namesAndStylesDict, funName)
		// f.write('}\n')
		// appendLatexFigureEnd(sb, br,name);

		for (final String tool : tools) {
			// make table header
			sb.append("\\begin{longtabu} to \\linewidth {lcllc");
			for (int i = 0; i < mLatexTableHeaderCount; ++i) {
				sb.append("r");
			}
			sb.append("}").append(br);
			sb.append("\\toprule").append(br);
			sb.append("  \\header{}& ").append(br);
			sb.append("  \\header{\\#}&").append(br);
			sb.append("  \\header{Result}&").append(br);
			sb.append("  \\header{Variant}& ").append(br);
			sb.append("  \\header{Count}&").append(br);

			int i = 0;
			for (final ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getLatexColumnTitle() == null) {
					continue;
				}
				sb.append("  \\header{");
				sb.append(removeInvalidCharsForLatex(cd.getLatexColumnTitle()));
				sb.append("}");
				i++;
				if (i < mLatexTableHeaderCount) {
					sb.append("&");
				} else {
					sb.append("\\\\");
				}
				sb.append(br);
			}
			sb.append("  \\cmidrule(r){2-");
			sb.append(5 + mLatexTableHeaderCount);
			sb.append("}").append(br);

			// make table body
			final PartitionedResults resultsPerTool =
					partitionResults(CoreUtil.where(results.All, new ITestSummaryResultPredicate() {
						@Override
						public boolean test(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().getName().equals(tool);
						}
					}));

			// end table
			sb.append("\\caption{Results for ").append(removeInvalidCharsForLatex(tool)).append(".}").append(br);
			sb.append("\\end{longtabu}").append(br);
		}

		// append finishing code
		appendEnd(sb, br);
	}

	// private void appendLatexFigureBegin(StringBuilder sb, String br) {
	// sb.append("\\onecolumn").append(br);
	// sb.append("\\begin{figure}").append(br);
	// sb.append("\\centering").append(br);
	// sb.append(" \\begin{tikzpicture}").append(br);
	// sb.append(" \\begin{customlegend}[legend columns=' + str(len(namesAndStyles) / 2) + ',legend
	// style={align=left,draw=none,column sep=2ex,thick},").append(br);
	// sb.append(" legend entries={' + legendentriesstr + '}]").append(br);
	// for name, (file, style) in namesAndStyles:
	// sb.append(" \\addlegendimage{' + style + '}").append(br);
	// sb.append(" \\end{customlegend}").append(br);
	// sb.append(" \\end{tikzpicture}").append(br);
	//
	// }

	private void appendEnd(final StringBuilder sb, final String br) {
		sb.append("\\end{document}").append(br);
	}

	private void appendPreamble(final StringBuilder sb, final String br) {
		// append preamble
		sb.append("\\documentclass{article}").append(br);
		sb.append("\\usepackage[table,dvipsnames]{xcolor}").append(br);
		sb.append("\\usepackage[utf8]{inputenc}").append(br);
		sb.append("\\usepackage{pgfplots}").append(br);
		sb.append("\\usepackage{pgfkeys}").append(br);
		sb.append("\\usepackage{xspace}").append(br);
		sb.append(br);

		// table commands
		sb.append("\\newcommand{\\headcolor}{}").append(br);
		sb.append("\\newcommand{\\header}[1]{\\parbox{2.8em}{\\centering #1}\\headcolor}").append(br);
		sb.append("\\newcommand{\\folder}[1]{\\parbox{5em}{#1}}").append(br);

		// commands for plots
		sb.append("% argument #1: any options").append(br);
		sb.append("\\newenvironment{customlegend}[1][]{%").append(br);
		sb.append("    \\begingroup").append(br);
		sb.append("    % inits/clears the lists (which might be populated from previous").append(br);
		sb.append("    % axes):").append(br);
		sb.append("    \\csname pgfplots@init@cleared@structures\\endcsname").append(br);
		sb.append("    \\pgfplotsset{#1}%").append(br);
		sb.append("}{%").append(br);
		sb.append("    % draws the legend:").append(br);
		sb.append("    \\csname pgfplots@createlegend\\endcsname").append(br);
		sb.append("    \\endgroup").append(br);
		sb.append("}%").append(br);
		sb.append(br);
		sb.append("% makes \\addlegendimage available (typically only available within an").append(br);
		sb.append("% axis environment):").append(br);
		sb.append("\\def\\addlegendimage{\\csname pgfplots@addlegendimage\\endcsname}").append(br);
		sb.append(br);
		sb.append("\\pgfplotsset{every axis/.append style={thick}}").append(br);
		sb.append(br);

		sb.append("\\definecolor{s1}{RGB}{228,26,28}").append(br);
		sb.append("\\definecolor{s2}{RGB}{55,126,184}").append(br);
		sb.append("\\definecolor{s3}{RGB}{77,175,74}").append(br);
		sb.append("\\definecolor{s4}{RGB}{152,78,163}").append(br);
		sb.append("\\definecolor{s5}{RGB}{255,127,0}").append(br);
		sb.append("\\definecolor{s6}{RGB}{255,255,51}").append(br);
		sb.append("\\definecolor{s7}{RGB}{166,86,40}").append(br);
		sb.append("\\definecolor{s8}{RGB}{247,129,191}").append(br);
		sb.append("\\definecolor{s9}{RGB}{153,153,153}").append(br);

		sb.append("\\pgfplotsset{").append(br);
		sb.append("    mark repeat/.style={").append(br);
		sb.append("        scatter,").append(br);
		sb.append("        scatter src=x,").append(br);
		sb.append("        scatter/@pre marker code/.code={").append(br);
		sb.append("            \\pgfmathtruncatemacro\\usemark{").append(br);
		sb.append("                or(mod(\\coordindex,#1)==0, (\\coordindex==(\\numcoords-1))").append(br);
		sb.append("            }").append(br);
		sb.append("            \\ifnum\\usemark=0").append(br);
		sb.append("                \\pgfplotsset{mark=none}").append(br);
		sb.append("            \\fi").append(br);
		sb.append("        },").append(br);
		sb.append("        scatter/@post marker code/.code={}").append(br);
		sb.append("    }").append(br);
		sb.append("}").append(br);

		sb.append("\\pgfplotsset{cycle list={%").append(br);
		for (final String style : getLatexPlotStyles()) {
			sb.append("{").append(style).append("},").append(br);
		}
		sb.append("}}").append(br);
		sb.append(br);

		sb.append("\\begin{document}").append(br);
	}

	private List<String> getLatexPlotStyles() {
		// plotstylesLines = zip(mLatexColors, mLatexPlotLines)
		// plotstylesMarks = zip(mLatexColors[len(mLatexPlotLines):], mLatexPlotMarks)
		// acc = []
		// for color, linestyle in plotstylesLines:
		// acc.append('draw=' + color + ',' + linestyle)
		// for color, markstyle in plotstylesMarks:
		// acc.append('mark repeat={' + str(mLatexPlotMarkRepeat) + '},draw=' + color + ',solid,mark=' + markstyle)
		// for color in mLatexColors[len(plotstylesLines) + len(plotstylesMarks):]:
		// acc.append('draw=' + color + ',solid')
		// return acc

		final List<String> rtr = new ArrayList<String>();

		return rtr;
	}

	private static final class PlotStyleProvider {
		// # Those are the presets s1 to s9 and all the remaining dvips colors of xcolor
		private static final String[] LATEX_COLORS = new String[] { "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8",
				"s9", "Black", "OliveGreen", "Apricot", "Aquamarine", "Bittersweet", "Blue", "BlueGreen", "BlueViolet",
				"BrickRed", "Brown", "BurntOrange", "CadetBlue", "CarnationPink", "Cerulean", "CornflowerBlue", "Cyan",
				"Dandelion", "DarkOrchid", "Emerald", "ForestGreen", "Fuchsia", "Goldenrod", "Gray", "Green",
				"GreenYellow", "JungleGreen", "Lavender", "LimeGreen", "Magenta", "Mahogany", "Maroon", "Melon",
				"MidnightBlue", "Mulberry", "NavyBlue", "Orange", "OrangeRed", "Orchid", "Peach", "Periwinkle",
				"PineGreen", "Plum", "ProcessBlue", "Purple", "RawSienna", "Red", "RedOrange", "RedViolet", "Rhodamine",
				"RoyalBlue", "RoyalPurple", "RubineRed", "Salmon", "SeaGreen", "Sepia", "SkyBlue", "SpringGreen", "Tan",
				"TealBlue", "Thistle", "Turquoise", "Violet", "VioletRed", "White", "WildStrawberry", "Yellow",
				"YellowGreen", "YellowOrange" };

		private static final String[] LATEX_MARKS =
				new String[] { null, "star", "triangle", "diamond", "x", "|", "10-pointed-star", "pentagon", "o" };
		private static final String[] LATEX_LINES = new String[] { "solid", "dotted", "dashed" };

		private static final int LATEX_PLOT_MARK_REPEAT = 10;

		private final String mColor;
		private final String mLinestyle;
		private final String mMarkstyle;

		private PlotStyleProvider(final String color, final String linestyle, final String markstyle) {
			mColor = color;
			mLinestyle = linestyle;
			mMarkstyle = markstyle;
		}

		private static List<PlotStyleProvider> getPlotStyles(final int totalStyles) {
			final List<PlotStyleProvider> rtr = new ArrayList<>();

			int color = 0;
			int line = 0;
			int mark = 0;
			while (rtr.size() < totalStyles) {
				rtr.add(new PlotStyleProvider(LATEX_COLORS[color], LATEX_LINES[line], LATEX_MARKS[mark]));

				color = (color + 1) % LATEX_COLORS.length;
				if (mark == 0) {
					line = (line + 1) % LATEX_LINES.length;
				}
				if (line == 0) {
					mark = (mark + 1) % LATEX_MARKS.length;
				}
			}
			return rtr;
		}

		private String getMarkstyle() {
			return mMarkstyle;
		}

		private String getLinestyle() {
			return mLinestyle;
		}

		private String getColor() {
			return mColor;
		}

		private String getMarkRepeat() {
			return String.valueOf(LATEX_PLOT_MARK_REPEAT);
		}

	}
}
