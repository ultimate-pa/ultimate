/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.annotations.IRSDependenciesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.annotations.UseDefSequence;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.RCFGWalkerUnroller;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.utils.Utils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class SequencingVisitor extends SimpleRCFGVisitor {

	private final RCFGWalkerUnroller mWalker;

	private final HashSet<String> mInputs;
	private final HashSet<String> mOutputs;
	private final HashMap<List<IcfgEdge>, List<Tuple<Tuple<Integer>>>> mDebugZoneMap;

	public SequencingVisitor(final RCFGWalkerUnroller w, final ILogger logger) {
		super(logger);
		mWalker = w;
		mInputs = new HashSet<>();
		mOutputs = new HashSet<>();
		mInputs.add("~input1");
		mInputs.add("~input2");
		mOutputs.add("~output1");
		mOutputs.add("~output2");
		mDebugZoneMap = new HashMap<>();
	}

	protected List<IcfgEdge> getCurrentPrefix() {
		return mWalker.getCurrentPrefix();
	}

	@Override
	public void endOfTrace() {
		super.endOfTrace();
		RealSequencingEOT();
		DebugSequencingEOT();
	}

	@Override
	public void finish() {
		super.finish();
		DebugFinish();

	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean abortCurrentBranch() {
		return false;
	}

	@Override
	public boolean abortAll() {
		return false;
	}

	private void RealSequencingEOT() {
		final List<IcfgEdge> trace = getCurrentPrefix();

		HashSet<String> remainingInputs = new HashSet<>(mInputs);
		HashSet<String> remainingOutputs = new HashSet<>(mOutputs);

		ZoneAnnotation currentZone = null;

		final boolean startFound = false;
		boolean endFound = false;
		boolean zoneShift = true;
		boolean isStable = true;

		for (final IcfgEdge currentEdge : trace) {
			final UseDefSequence ud = UseDefSequence.getAnnotation(currentEdge,
					UseDefSequence.class);
			if (ud != null) {

				final List<Statement> stmts = extractStatements(currentEdge);

				for (int j = 0; j < ud.Sequence.size(); j++) {
					final UseDefSet uds = ud.Sequence.get(j);

					if (zoneShift) {
						if (currentZone != null) {
							currentZone.EndEdge = currentEdge;
							currentZone.EndStatement = stmts.get(j);
						}
						currentZone = new ZoneAnnotation();
						currentZone.StartEdge = currentEdge;
						currentZone.StartStatement = stmts.get(j);

						remainingInputs = new HashSet<>(mInputs);
						remainingOutputs = new HashSet<>(mOutputs);

						zoneShift = false;
					}

					final boolean removedInput = remainingInputs.removeAll(uds.Use);
					final boolean removedOutput = remainingOutputs.removeAll(uds.Def);

					if (removedInput || removedOutput) {
						if (isStable) {
							isStable = false;
							zoneShift = true;
						}
					}

					if (endFound) {
						final HashSet<String> readInputs = Utils.intersect(uds.Use,
								mInputs);
					}

					if (remainingInputs.isEmpty() && remainingOutputs.isEmpty()
							&& !endFound) {
						endFound = true;
						zoneShift = true;
					}

				}
				currentZone.addAnnotation(currentEdge);
			}
		}
	}

	private List<Statement> extractStatements(final IcfgEdge e) {
		if (e instanceof StatementSequence) {
			return ((StatementSequence) e).getStatements();
		} else if (e instanceof Call) {
			final ArrayList<Statement> rtr = new ArrayList<>();
			rtr.add(((Call) e).getCallStatement());
			return rtr;
		} else {
			return new ArrayList<>();
		}
	}

	private void DebugSequencingEOT() {
		final List<IcfgEdge> trace = getCurrentPrefix();

		final List<Tuple<Tuple<Integer>>> zones = new ArrayList<>();

		Tuple<Integer> start = new Tuple<Integer>(0, 0);
		Tuple<Integer> end = new Tuple<Integer>(0, 0);
		final Tuple<Integer> last = new Tuple<Integer>(0, 0);

		HashSet<String> remainingInputs = new HashSet<>(mInputs);
		HashSet<String> remainingOutputs = new HashSet<>(mOutputs);

		boolean searchForRealEnd = false;
		boolean startFound = false;

		for (int i = 0; i < trace.size(); ++i) {
			final UseDefSequence ud = UseDefSequence.getAnnotation(trace.get(i),
					UseDefSequence.class);
			if (ud != null) {
				for (int j = 0; j < ud.Sequence.size(); j++) {
					final UseDefSet uds = ud.Sequence.get(j);

					if (searchForRealEnd) {
						final HashSet<String> readInputs = Utils.intersect(uds.Use,
								mInputs);

						if (!readInputs.isEmpty()) {
							remainingInputs = new HashSet<>(mInputs);
							remainingOutputs = new HashSet<>(mOutputs);
							end = new Tuple<>(last);
							zones.add(new Tuple<SequencingVisitor.Tuple<Integer>>(
									start, end));
							start = new Tuple<Integer>(end);
							end = new Tuple<>(end);
							searchForRealEnd = false;
							startFound = false;
						}
					}

					if (!startFound) {
						startFound = remainingInputs.removeAll(uds.Use);
						if (startFound) {
							start.set(i, j);
						}
					} else {
						remainingInputs.removeAll(uds.Use);
					}

					remainingOutputs.removeAll(uds.Def);

					if (remainingInputs.isEmpty() && remainingOutputs.isEmpty()
							&& !searchForRealEnd) {
						end.set(i, j);
						searchForRealEnd = true;
					}

					last.set(i, j);
				}
			}
		}
		if (start.compareTo(end) == -1) {
			zones.add(new Tuple<SequencingVisitor.Tuple<Integer>>(start, end));
		}
		// sLogger.debug(insertLineBreaks(200, traceToString(trace)));
		mDebugZoneMap.put(new ArrayList<>(trace), zones);
	}

	private void DebugFinish() {
		final StringBuilder outer = new StringBuilder();

		outer.append("List of zones:\n");
		for (final Entry<List<IcfgEdge>, List<Tuple<Tuple<Integer>>>> e : mDebugZoneMap
				.entrySet()) {
			int i = 0;
			final StringBuilder inner = new StringBuilder();
			for (final IcfgEdge edge : e.getKey()) {
				final ZoneAnnotation za = IRSDependenciesAnnotation.getAnnotation(
						edge, ZoneAnnotation.class);
				if (za != null) {
					outer.append(za).append(";");
				}
				inner.append("(").append(i).append(") ");
				inner.append(Utils.edgeToString(edge));
				inner.append(" ");
				++i;
			}
			outer.append("\n");
			outer.append(Utils.insertLineBreaks(200, inner.toString()));
			outer.append("\n");

			for (final Tuple<Tuple<Integer>> zone : e.getValue()) {
				outer.append(zone.First.First).append(",")
						.append(zone.First.Last);
				outer.append(" - ");
				outer.append(zone.Last.First).append(",")
						.append(zone.Last.Last);
				outer.append("   ");
			}
			outer.append("\n----------------------------------------\n");
		}

		mLogger.debug(outer.toString());

	}

	private class ZoneAnnotation extends IRSDependenciesAnnotation {

		private static final long serialVersionUID = 1L;
		private IcfgEdge StartEdge;
		private Statement StartStatement;

		private IcfgEdge EndEdge;
		private Statement EndStatement;

		private boolean IsStable;

		@Override
		protected String[] getFieldNames() {
			return new String[] {};
		}

		@Override
		protected Object getFieldValue(final String field) {
			// TODO Auto-generated method stub
			return null;
		}

		private void addOrMergeAnnotation(final IElement e) {
			final ZoneAnnotation za = getAnnotation(e, this.getClass());
			if (za != null) {
				if (!za.equals(this)) {
					// merge
					mLogger.debug("Need to merge: " + this + " with " + za);
				}

			} else {
				// add
				addAnnotation(e);
			}
		}

		@Override
		public String toString() {
			if (StartStatement == null || EndStatement == null) {
				return "Invalid Zone";
			}

			if (IsStable) {
				return "Stable: Start " + StartStatement.toString() + " End "
						+ EndStatement.toString();
			} else {
				return "Unstable: Start " + StartStatement.toString() + " End "
						+ EndStatement.toString();
			}

		}

	}

	private final class Tuple<T extends Comparable<T>> implements
			Comparable<Tuple<T>> {
		T First;
		T Last;

		Tuple(final T first, final T last) {
			set(first, last);
		}

		Tuple(final Tuple<T> tuple) {
			set(tuple.First, tuple.Last);
		}

		private void set(final T first, final T last) {
			First = first;
			Last = last;
		}

		@Override
		public boolean equals(final Object arg0) {
			if (arg0 instanceof Tuple<?>) {
				return First.equals(((Tuple<?>) arg0).First)
						&& Last.equals(((Tuple<?>) arg0).Last);
			}
			return super.equals(arg0);
		}

		@Override
		public int compareTo(final Tuple<T> t) {
			if (First.compareTo(t.First) == 0) {
				return Last.compareTo(t.Last);
			} else {
				return First.compareTo(t.First);
			}
		}
	}

}
