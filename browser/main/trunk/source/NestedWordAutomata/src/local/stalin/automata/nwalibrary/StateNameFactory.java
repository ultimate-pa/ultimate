package local.stalin.automata.nwalibrary;

import java.util.Collection;

public class StateNameFactory extends ContentFactory<String> {

	@Override
	public String createContentOnIntersection(String c1, String c2) {

		return new String("[" + c1 + ", " + c2 + "]");
	}

	@Override
	public String createContentOnDeterminization(
			Collection<Pair<String, String>> cPairList) {
		String result = "{";
		boolean first = true;
		for (Pair<String, String> cPair : cPairList) {
			if (first)
				first = false;
			else
				result += ", ";
			result += "(" + cPair.fst + ", " + cPair.snd + ")";
		}
		result += "}";

		return result;
	}

	@Override
	public String createContentOnDifference(String c1,
			Collection<Pair<String, String>> cPairList) {

		String tempString = "{";
		if (cPairList != null) {
			boolean first = true;
			for (Pair<String, String> cPair : cPairList) {
				if (first)
					first = false;
				else
					tempString += ", ";
				tempString += "(" + cPair.fst + ", " + cPair.snd + ")";
			}
		} else
			tempString += "Empty";
		tempString += "}";

		return new String("[" + c1 + ", " + tempString + "]");
	}
	
	@Override
	public String createSinkStateContent() {
		return new String("SinkState");
	}
	
	@Override
	public String createEmptyStackContent() {
		return "EmptyStack";
	}

	
	
	@Override
	public String getContentOnPetriNet2FiniteAutomaton(Collection<String> cList) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean firstElement = true;
		for (String content :cList) {
			if (firstElement) {
				firstElement = false;
			}
			else {
				sb.append(",");
			}
			sb.append(content);
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
	
	
	
	
}
