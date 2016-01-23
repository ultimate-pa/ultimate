package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;

public class BoogieAstUtil {

	public static IBoogieVar createTemporaryIBoogieVar(String identifier, IType type) {
		return new IBoogieVar() {
			@Override
			public String getIdentifier() {
				return identifier;
			}

			@Override
			public IType getIType() {
				return type;
			}

			@Override
			public ApplicationTerm getDefaultConstant() {
				throw new UnsupportedOperationException("Temporary IBoogieVars dont have default constants.");
			}
		};
	}
	
}
