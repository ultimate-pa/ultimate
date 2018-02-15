package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 *
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 */
public class InitializationPattern extends PatternType {

	public enum VarAccess {
		IN, OUT, HIDDEN, CONST
	}

	private final String mType;
	private final VarAccess mVisibility;
	private final String mIdent;

	public InitializationPattern(final String ident, final String type, final VarAccess visibility) {
		this(ident, type, visibility, null);
	}

	public InitializationPattern(final String ident, final String type, final VarAccess visibility,
			final CDD initially) {
		mIdent = ident;
		mType = type;
		mVisibility = visibility;

		if (initially != null) {
			mergeCDDs(Collections.singletonList(initially));
		}
	}

	public VarAccess getAccessability() {
		return mVisibility;
	}

	public String getIdent() {
		return mIdent;
	}

	public String getType() {
		return mType;
	}
}
