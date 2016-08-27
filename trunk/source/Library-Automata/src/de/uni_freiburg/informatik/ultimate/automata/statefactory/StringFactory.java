/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.StateWithRankInfo;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class StringFactory implements IStateFactory<String> {

	@Override
	public String intersection(final String s1, final String s2) {
  		final StringBuilder sb = new StringBuilder("[");
  		sb.append(s1).append(", ").append(s2).append("]");
  		return sb.toString();
	}
	
	@Override
	public String intersectBuchi(final String s1, final String s2, final int track) {
		final StringBuilder sb = new StringBuilder("[");
		sb.append(s1).append(", ").append(s2).append(", track").append(track).append("]");
		return sb.toString();
	}

	@Override
	public String determinize(final Map<String, Set<String>> down2up) {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (final Entry<String, Set<String>> entry : down2up.entrySet()) {
			final String down = entry.getKey();
			final Iterator<String> it = entry.getValue().iterator();
			String up = it.next();
			sb.append("(").append(down).append(",").append(up).append(")");
			while (it.hasNext()) {
				up = it.next();
				sb.append(", ");
				sb.append("(").append(down).append(",").append(up).append(")");
			}
		}
		sb.append("}");
		return sb.toString();
	}

	@Override
	public String createSinkStateContent() {
		return new String("∅SinkState");
	}
	
	@Override
	public String createEmptyStackState() {
		return "€";
	}

	
	
//	@Override
//	public String getContentOnPetriNet2FiniteAutomaton(Collection<String> cList) {
//		StringBuilder sb = new StringBuilder();
//		sb.append("{");
//		boolean firstElement = true;
//		for (String content :cList) {
//			if (firstElement) {
//				firstElement = false;
//			}
//			else {
//				sb.append(",");
//			}
//			sb.append(content);
//		}
//		sb.append("}");
//		return sb.toString();
//	}

	
	
	@Override
	public String getContentOnPetriNet2FiniteAutomaton(final Marking<?, String> marking) {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean firstElement = true;
		for (final Place<?, String> place  : marking) {
			if (firstElement) {
				firstElement = false;
			} else {
				sb.append(",");
			}
			sb.append(place.getContent());
		}
		sb.append("}");
		return sb.toString();
	}


	@Override
	public String getBlackContent(final String c) {
		return "Black:" + c;
	}


	@Override
	public String getWhiteContent(final String c) {
		return "White:" + c;
	}
	
	@Override
	public String buchiComplementFKV(final LevelRankingState<?, String> compl) {
		if (compl.isNonAcceptingSink()) {
			return compl.toString();
		}
		
		final boolean isNestedWordAutomaton =
				!compl.getOperand().getCallAlphabet().isEmpty();
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (final StateWithRankInfo<String> down : compl.getDownStates()) {
			for (final StateWithRankInfo<String> up : compl.getUpStates(down)) {
				sb.append("(");
				if (isNestedWordAutomaton) {
					sb.append(down.getState());
					sb.append(",");
					if (down.hasRank()) {
						sb.append(down.getRank());
						if (down.isInO()) {
							sb.append("X");
						}
					} else {
						sb.append("∞");
					}
					sb.append(",");
				}
				sb.append(up.getState());
				sb.append(",");
				if (up.hasRank()) {
					sb.append(up.getRank());
					if (up.isInO()) {
						sb.append("X");
					}
				} else {
					sb.append("∞");
				}
				sb.append(")");
			}
		}
		sb.append("}");
		return sb.toString();
	}
	
	
	
	@Override
	public String buchiComplementNCSB(final LevelRankingState<?, String> compl) {
		if (compl.isNonAcceptingSink()) {
			return compl.toString();
		}
		
		final List<Pair<StateWithRankInfo<String>,String>> n = new ArrayList<Pair<StateWithRankInfo<String>,String>>();
		final List<Pair<StateWithRankInfo<String>,String>> c = new ArrayList<Pair<StateWithRankInfo<String>,String>>();
		final List<Pair<StateWithRankInfo<String>,String>> s = new ArrayList<Pair<StateWithRankInfo<String>,String>>();
		final List<Pair<StateWithRankInfo<String>,String>> b = new ArrayList<Pair<StateWithRankInfo<String>,String>>();
		
		for (final StateWithRankInfo<String> down : compl.getDownStates()) {
			for (final StateWithRankInfo<String> up : compl.getUpStates(down)) {
				if (up.hasRank()) {
					if (up.getRank() == 3) {
						n.add(new Pair<StateWithRankInfo<String>,String>(down, up.getState()));
					} else if (up.getRank() == 2) {
						c.add(new Pair<StateWithRankInfo<String>,String>(down, up.getState()));
						if (up.isInO()) {
							b.add(new Pair<StateWithRankInfo<String>,String>(down, up.getState()));
						}
					} else if (up.getRank() == 1) {
						s.add(new Pair<StateWithRankInfo<String>,String>(down, up.getState()));
					} else {
						throw new IllegalArgumentException("only 1,2,3");
					}
				} else {
					throw new IllegalArgumentException("must have rank");
				}
			}
		}
		final boolean isNestedWordAutomaton =
				!compl.getOperand().getCallAlphabet().isEmpty();
		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(prettyprintCollectionOfStates(n,isNestedWordAutomaton));
		sb.append(",");
		sb.append(prettyprintCollectionOfStates(c,isNestedWordAutomaton));
		sb.append(",");
		sb.append(prettyprintCollectionOfStates(s,isNestedWordAutomaton));
		sb.append(",");
		sb.append(prettyprintCollectionOfStates(b,isNestedWordAutomaton));
		sb.append(")");
		return sb.toString();
	}
	
	

	private String prettyprintCollectionOfStates(
			final List<Pair<StateWithRankInfo<String>,String>> collection,
			final boolean isNestedWordAutomaton) {
		if (collection.isEmpty()) {
			return "{}";
		} else {
			final StringBuilder sb = new StringBuilder();
			sb.append("{");
			boolean isFirst = true;
			for (final Pair<StateWithRankInfo<String>,String> dd : collection) {
				if (isFirst) {
					isFirst = false;
				} else {
					sb.append(",");
				}
				if (isNestedWordAutomaton) {
					sb.append("(");
					sb.append(dd.getFirst());
					sb.append(",");
					sb.append(dd.getSecond());
					sb.append(")");
				} else {
					sb.append(dd.getSecond());
				}
			}
			sb.append("}");
			return sb.toString();
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ContentFactory#complementBuchiDeterministicNonFinal(java.lang.Object)
	 */
	@Override
	public String complementBuchiDeterministicNonFinal(final String c) {
		// TODO Auto-generated method stub
		return "NonFinal:" + c;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ContentFactory#complementBuchiDeterministicFinal(java.lang.Object)
	 */
	@Override
	public String complementBuchiDeterministicFinal(final String c) {
		return "Final:" + c;
	}
	
	@Override
	public String minimize(final Collection<String> states) {
		if (states == null) {
			return "{}";
		}
		final StringBuilder sb = new StringBuilder("{");
		for (final Iterator<String> it = states.iterator(); it.hasNext(); ) {
			sb.append(it.next());
			if (it.hasNext()) {
				sb.append(", ");
			}
		}
		return sb.append("}").toString();
	}

	@Override
	public String createDoubleDeckerContent(final String down, final String up) {
		return "<" + down + "," + up + ">";
	}

	@Override
	public String constructBuchiSVWState(final Integer stateNb, final Integer tmaNb) {
		final StringBuilder sb = new StringBuilder("(");
		sb.append(stateNb);
		sb.append(",");
		sb.append(tmaNb);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public String finitePrefix2net(final Condition<?, String> c) {
		return c.toString();
	}
	
	@Override
	public String senwa(final String entry, final String state) {
		final String result = state + " (entry " + entry + ")";
		return result;
	}
}
