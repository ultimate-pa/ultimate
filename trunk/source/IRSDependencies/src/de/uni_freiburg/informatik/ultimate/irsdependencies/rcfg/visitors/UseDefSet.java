package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors;

import java.util.HashSet;

public class UseDefSet {

	public HashSet<String> Use;
	public HashSet<String> Def;

	UseDefSet() {
		Use = new HashSet<>();
		Def = new HashSet<>();
	}

	private UseDefSet(UseDefSet set) {
		this();
		Use.addAll(set.Use);
		Def.addAll(set.Def);
	}

	private boolean isEmpty() {
		return Use.isEmpty() && Def.isEmpty();
	}

	UseDefSet merge(UseDefSet set) {
		if (this.isEmpty()) {
			return new UseDefSet(set);
		}

		if (set.isEmpty()) {
			return new UseDefSet(this);
		}

		UseDefSet rtr = new UseDefSet();
		rtr.Use.addAll(Use);
		rtr.Use.addAll(set.Use);
		rtr.Def.addAll(Def);
		rtr.Def.addAll(set.Def);
		return rtr;
	}

	@Override
	public String toString() {
		return "Use=" + Use.toString() + ",Def=" + Def.toString();
	}
}