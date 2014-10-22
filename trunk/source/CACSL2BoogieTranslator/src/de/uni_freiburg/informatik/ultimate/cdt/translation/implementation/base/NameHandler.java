/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.03.2012
 */
public class NameHandler implements INameHandler {
	/**
	 * Counter for temporary variables.
	 */
	private int mTmpUID;
	
	private int mGlobalCounter;
	
	private final CACSL2BoogieBacktranslator mBacktranslator;

	public NameHandler(CACSL2BoogieBacktranslator backtranslator){
		mBacktranslator = backtranslator;
	}
	
	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Override
	public Result visit(Dispatcher main, IASTNode node) {
		throw new UnsupportedOperationException(
				"Implementation Error: Use C handler for " + node.getClass());
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Override
	public Result visit(Dispatcher main, ACSLNode node) {
		throw new UnsupportedOperationException(
				"Implementation error: Use ACSL handler for " + node.getClass());
	}
	
	

	@Override
	public String getUniqueIdentifier(IASTNode scope, String cId, int compCnt, boolean isOnHeap) {
		final String boogieId;
		{ //special case struct field identifier
			// if some parent is IASTCompositeTypeSpecifier we need indentifier for 
			// field of struct, field of union, or constant of enum
			// we return the original name.
			IASTNode curr = scope; // TODO : is there a better way to do that?
			while (curr != null
					&& !(curr.getParent() instanceof IASTTranslationUnit)) {
				if (curr instanceof IASTCompositeTypeSpecifier) {
					boogieId = cId;
					mBacktranslator.putVar(boogieId, cId);
					return boogieId;
				}
				curr = curr.getParent();
			}
		}
		assert cId.length() > 0 : "Empty C identifier";
		assert (compCnt >= 0);
		// mark variables that we put on the heap manually (bc they are addressoffed)
		// with a "#"
		String onHeapStr = "";
		if (isOnHeap)
			onHeapStr = "#";
		// add tilde to identifier and the compound counter if variable is not 
		// used in the lowest compound nesting level (compCnt==0)
		if (compCnt > 0) {
			boogieId = "~" + onHeapStr + cId + "~" + compCnt;
		} else {
			boogieId = "~" + onHeapStr + cId;
		}
		mBacktranslator.putVar(boogieId, cId);
		return boogieId;
	}
	
	@Override
	public String getInParamIdentifier(String cId) {
		//(alex:) in case of several unnamed parameters we need uniqueness 
		//(still a little bit overkill, to make it precise we would need to check whether 
		// the current method has more than one unnamed parameter)
		final String boogieId = SFO.IN_PARAM + cId + (cId.isEmpty() ? mTmpUID++ : ""); 
		mBacktranslator.putInVar(boogieId, cId);
		return boogieId;
	}

	@Override
	public String getTempVarUID(SFO.AUXVAR purpose) {
		final String boogieId = SFO.TEMP + purpose.getId() + mTmpUID++;
		mBacktranslator.putTempVar(boogieId, purpose);
		return boogieId;
	}

	@Override
	public String getGloballyUniqueIdentifier(String looplabel) {
		return looplabel + mGlobalCounter++;
	}

	@Override
	public boolean isTempVar(String boogieId) {
		return mBacktranslator.isTempVar(boogieId);
	}
}
