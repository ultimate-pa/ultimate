package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * A GlobalBoogieVar is either a OldBoogieVar or a NonOldBoogieVar.
 * The NonOldBoogieVar is a variable that can be modified in the program.
 * The OldBoogieVar is a variable that has always the value that the 
 * corresponding NonOldBoogieVar had at the beginning of the last procedure
 * call.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class GlobalBoogieVar extends BoogieVar implements Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	
	public GlobalBoogieVar(String identifier, IType iType, 
			TermVariable tv,
			ApplicationTerm defaultConstant,
			ApplicationTerm primedContant) {
		super(identifier, iType, tv, defaultConstant, primedContant);
	}
	
	public String getProcedure() {
		return null;
	}

	public boolean isGlobal() {
		return true;
	}
}
