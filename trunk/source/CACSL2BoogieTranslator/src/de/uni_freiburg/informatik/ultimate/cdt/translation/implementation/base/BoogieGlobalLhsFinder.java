package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;

/**
 * Looks for a VariableLHS with a global variable inside a given LHS.
 * Returns such a VariableLHS if it exists, null otherwise.
 * Note that this will crash if the VariableLHS does not contain a DeclarationInformation.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class BoogieGlobalLhsFinder extends BoogieVisitor {

	private VariableLHS mResult;

	@Override
	protected void visit(final VariableLHS lhs) {
		if (lhs.getDeclarationInformation().getStorageClass() == StorageClass.GLOBAL) {
			if (mResult != null) {
				throw new AssertionError("there should be at most one VariableLHS inside a LeftHandSide!");
			} else {

				mResult = lhs;// lhs.getIdentifier();
			}
		}
		super.visit(lhs);
	}

	public VariableLHS getGlobalId(final LeftHandSide lhs) {
		super.processLeftHandSide(lhs);
		return mResult;
	}
}