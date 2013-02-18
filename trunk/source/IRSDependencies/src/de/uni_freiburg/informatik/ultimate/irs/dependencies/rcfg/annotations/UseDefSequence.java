package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.annotations;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.visitors.UseDefSet;

public class UseDefSequence extends IRSDependenciesAnnotation {

	private static final long serialVersionUID = 1L;
	public List<UseDefSet> Sequence;

	public UseDefSequence() {
		Sequence = new ArrayList<>();
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] { "Sequence" };
	}

	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "Sequence":
			if (Sequence.isEmpty()) {
				return "Sequence is empty";
			}
			return Sequence;
		default:
			return null;
		}
	}

}