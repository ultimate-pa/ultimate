package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;

public class StringFactory extends StateFactory<String> {

	@Override
	public String intersection(String s1, String s2) {
  		StringBuilder sb = new StringBuilder("[");
  		sb.append(s1).append(", ").append(s2).append("]");
  		return sb.toString();
	}
	
	public String intersectBuchi(String s1, String s2, int track) {
		StringBuilder sb = new StringBuilder("[");
		sb.append(s1).append(", ").append(s2).append(", track").append(track).append("]");
		return sb.toString();
	}

	@Override
	public String determinize(Map<String, Set<String>> down2up) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (String down : down2up.keySet()) {
			Iterator<String> it = down2up.get(down).iterator();
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
	public String getContentOnPetriNet2FiniteAutomaton(Marking<?, String> marking) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean firstElement = true;
		for (Place<?, String> place  : marking) {
			if (firstElement) {
				firstElement = false;
			}
			else {
				sb.append(",");
			}
			sb.append(place.getContent());
		}
		sb.append("}");
		return sb.toString();
	}


	@Override
	public String getBlackContent(String c) {
		return "Black:"+c;
	}


	@Override
	public String getWhiteContent(String c) {
		return "White:"+c;
	}
	
	@Override
	public String buchiComplementFKV(BuchiComplementFKV<?,String>.LevelRankingState compl) {
		
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (String down : compl.getDownStates()) {
			for (String up : compl.getUpStates(down)) {
				sb.append("(");
				sb.append(down);
				sb.append(",");
				sb.append(up);
				sb.append(",");
				sb.append(compl.getRank(down, up));
				if (compl.inO(down, up)) {
					sb.append("X");
				}
				sb.append(")");					
			}
		}
		sb.append("}");
		return sb.toString();
	}
	
	

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ContentFactory#complementBuchiDeterministicNonFinal(java.lang.Object)
	 */
	@Override
	public String complementBuchiDeterministicNonFinal(String c) {
		// TODO Auto-generated method stub
		return "NonFinal:"+c;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ContentFactory#complementBuchiDeterministicFinal(java.lang.Object)
	 */
	@Override
	public String complementBuchiDeterministicFinal(String c) {
		return "Final:"+c;
	}
	
	@Override
	public String minimize(Collection<String> states) {
		if(states == null) {
			return "{}";
		}
		StringBuilder sb = new StringBuilder("{");
		for(Iterator<String> it = states.iterator(); it.hasNext(); ) {
			sb.append(it.next());
			if(it.hasNext()) {
				sb.append(", ");
			}
		}
		return sb.append("}").toString();
	}

	@Override
	public String createDoubleDeckerContent(String down, String up) {
		return "<" + down + "," + up + ">"; 
	}

	@Override
	public String constructBuchiSVWState(Integer stateNb, Integer tmaNb) {
		StringBuilder sb = new StringBuilder("(");
		sb.append(stateNb);
		sb.append(",");
		sb.append(tmaNb);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public String finitePrefix2net(Condition<?, String> c) {
		return c.toString();
	}
	
	@Override
	public String senwa(String entry, String state) {
		String result = state + " (entry " + entry + ")";
		return result;
	}
	
}
