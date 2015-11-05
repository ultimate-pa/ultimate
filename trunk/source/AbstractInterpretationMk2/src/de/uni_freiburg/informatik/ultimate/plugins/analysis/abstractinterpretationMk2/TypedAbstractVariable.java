package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;

/**
 * @author Jan Hättig 
 */
public class TypedAbstractVariable extends AbstractVariable {
	private final IType mType;

	/**
	 * Create an abstract variable with type and declaration information
	 */
	public TypedAbstractVariable(String ident,
			DeclarationInformation declaration, IType type) {
		super(ident);
		assert ident != null;
		assert declaration != null;
		mDeclaration = declaration;
		mType = type;
	}

	public IType getType() {
		return mType;
	}

	@Override
	public String toString() {
		String s = super.toString();
		// if(mDeclaration != null)
		// {
		// s += "+".concat(mDeclaration.toString());
		// }
		// if(mType != null)
		// {
		// s += ":".concat(mType.toString());
		// }

		return s;
	}
	
	public Term getTermVar(final Boogie2SMT bpl2smt){
		final String id = getString();
		final DeclarationInformation declInfo = getDeclaration();
		assert id != null;
		assert declInfo != null;
		final BoogieVar bplvar = bpl2smt.getBoogie2SmtSymbolTable().getBoogieVar(id,
				declInfo, false);
		assert bplvar != null : "There is no BoogieVar for this constaint (maybe an old value?)";
		final TermVariable termvar = bplvar.getTermVariable();
		assert termvar != null : "There seems to be no termvar for this BoogieVar";
		return termvar;
	}
}
