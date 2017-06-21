package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class InitializationPattern extends PatternType {

	public enum VarAccess {
		in, out, hidden
	}

	private final String type;
	private final VarAccess visibility;
	private final String ident;

	public InitializationPattern(final String ident, final String type, final VarAccess visibility) {
		this.ident = ident;
		this.type = type;
		this.visibility = visibility;
	}

	public InitializationPattern(final String ident, final String type, final VarAccess visibility,
			final CDD initially) {
		this.ident = ident;
		this.type = type;
		this.visibility = visibility;

		final Vector<CDD> aux = new Vector<CDD>();
		aux.add(initially);
		mergeCDDs(aux);
	}

	public VarAccess getAccessability() {
		return visibility;
	}

	public String getIdent() {
		return ident;
	}

	public String getType() {
		return type;
	}

}
