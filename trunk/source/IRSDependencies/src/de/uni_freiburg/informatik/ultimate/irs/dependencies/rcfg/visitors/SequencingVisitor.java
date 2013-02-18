package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.visitors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.annotations.IRSDependenciesAnnotation;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.annotations.UseDefSequence;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker.RCFGWalkerUnroller;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.utils.Utils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class SequencingVisitor extends RCFGVisitor {

	private RCFGWalkerUnroller mWalker;

	private HashSet<String> mInputs;
	private HashSet<String> mOutputs;
	private HashMap<List<RCFGEdge>, List<Tuple<Tuple<Integer>>>> mDebugZoneMap;

	public SequencingVisitor(RCFGWalkerUnroller w) {
		mWalker = w;
		mInputs = new HashSet<>();
		mOutputs = new HashSet<>();
		mInputs.add("~input1");
		mInputs.add("~input2");
		mOutputs.add("~output1");
		mOutputs.add("~output2");
		mDebugZoneMap = new HashMap<>();
	}

	protected List<RCFGEdge> getCurrentPrefix() {
		return mWalker.getCurrentPrefix();
	}

	@Override
	public void endOfTrace() {
		super.endOfTrace();
		List<RCFGEdge> trace = getCurrentPrefix();

		List<Tuple<Tuple<Integer>>> zones = new ArrayList<>();

		Tuple<Integer> start = new Tuple<Integer>(0, 0);
		Tuple<Integer> end = new Tuple<Integer>(0, 0);
		Tuple<Integer> last = new Tuple<Integer>(0, 0);

		HashSet<String> remainingInputs = new HashSet<>(mInputs);
		HashSet<String> remainingOutputs = new HashSet<>(mOutputs);

		boolean searchForRealEnd = false;
		boolean startFound = false;

		for (int i = 0; i < trace.size(); ++i) {
			UseDefSequence ud = UseDefSequence.getAnnotation(trace.get(i),
					UseDefSequence.class);
			if (ud != null) {
				for (int j = 0; j < ud.Sequence.size(); j++) {
					UseDefSet uds = ud.Sequence.get(j);

					if (searchForRealEnd) {
						HashSet<String> readInputs = Utils.intersect(uds.Use, mInputs);

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

					if (remainingInputs.isEmpty() && remainingOutputs.isEmpty() && !searchForRealEnd) {
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
		//sLogger.debug(insertLineBreaks(200, traceToString(trace)));
		mDebugZoneMap.put(new ArrayList<>(trace), zones);
	}

	@Override
	public void finish() {
		super.finish();

		StringBuilder outer = new StringBuilder();

		outer.append("List of zones:\n");
		for (Entry<List<RCFGEdge>, List<Tuple<Tuple<Integer>>>> e : mDebugZoneMap
				.entrySet()) {
			int i = 0;
			StringBuilder inner = new StringBuilder();
			for (RCFGEdge edge : e.getKey()) {
				inner.append("(").append(i).append(") ");
				inner.append(Utils.edgeToString(edge));
				inner.append(" ");
				++i;
			}
			outer.append(Utils.insertLineBreaks(200, inner.toString()));
			outer.append("\n");

			for (Tuple<Tuple<Integer>> zone : e.getValue()) {
				outer.append(zone.First.First).append(",")
						.append(zone.First.Last);
				outer.append(" - ");
				outer.append(zone.Last.First).append(",")
						.append(zone.Last.Last);
				outer.append("   ");
			}
			outer.append("\n----------------------------------------\n");
		}

		sLogger.debug(outer.toString());

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
	
	private class ZoneAnnotation extends IRSDependenciesAnnotation{

		@Override
		protected String[] getFieldNames() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		protected Object getFieldValue(String field) {
			// TODO Auto-generated method stub
			return null;
		}
		
	}

	private class Tuple<T extends Comparable<T>> implements
			Comparable<Tuple<T>> {
		T First;
		T Last;

		private Tuple(T first, T last) {
			set(first, last);
		}

		private Tuple(Tuple<T> tuple) {
			set(tuple.First, tuple.Last);
		}

		private void set(T first, T last) {
			First = first;
			Last = last;
		}

		@Override
		public boolean equals(Object arg0) {
			if (arg0 instanceof Tuple<?>) {
				return First.equals(((Tuple<?>) arg0).First)
						&& Last.equals(((Tuple<?>) arg0).Last);
			}
			return super.equals(arg0);
		}

		@Override
		public int compareTo(Tuple<T> t) {
			if (First.compareTo(t.First) == 0) {
				return Last.compareTo(t.Last);
			} else {
				return First.compareTo(t.First);
			}
		}
	}

}
