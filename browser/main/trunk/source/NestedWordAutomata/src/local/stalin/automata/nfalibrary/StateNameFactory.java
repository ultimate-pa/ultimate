package local.stalin.automata.nfalibrary;

import java.util.HashSet;
import java.util.List;

import local.stalin.automata.nfalibrary.IStateContentFactory;
import local.stalin.automata.nfalibrary.StateName;

public class StateNameFactory implements IStateContentFactory<StateName> {

	@Override
	public StateName createContentOnIntersection(StateName c1, StateName c2) {
		String name = new String();
		name = "(" + c1.name + "," + c2.name + ")";
		return new StateName(name);
	}
	@Override
	public StateName createContentOnDeterminization(List<StateName> list) {
		String result = "q";
		HashSet<Character> set = new HashSet<Character>();
		for(StateName name : list)
			for(int i=1;i<name.getName().length();i++)
				set.add(name.getName().charAt(i));
		for(char c : set)
			result += c;
		return new StateName(result);
	}
	@Override
	public StateName createContentOnMinimization(List<StateName> list) {
		String result = "";
		for(StateName name : list)
			result = result + name.getName();
		return new StateName(result);
	}
	@Override
	public StateName createSinkStateContent() {
		return new StateName("sinkState");
	}
}
