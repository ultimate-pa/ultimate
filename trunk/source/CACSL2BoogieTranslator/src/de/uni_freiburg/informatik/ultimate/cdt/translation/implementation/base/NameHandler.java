/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

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
	private int tmpUID;

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
	
	private Boogie2C boogie2C = new Boogie2C();

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
					boogie2C.putVar(boogieId, cId);
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
		boogie2C.putVar(boogieId, cId);
		return boogieId;
	}
	
	@Override
	public String getInParamIdentifier(String cId) {
		final String boogieId = SFO.IN_PARAM + cId;
		boogie2C.putInVar(boogieId, cId);
		return boogieId;
	}

	@Override
	public String getTempVarUID(SFO.AUXVAR purpose) {
		final String boogieId = SFO.TEMP + purpose.getId() + tmpUID++;
		boogie2C.putTempVar(boogieId, purpose);
		return boogieId;
	}
	
	@Override
	public Boogie2C getBoogie2C() {
		return boogie2C;
	}
	
	@Override
	public boolean isTempVar(String boogieId) {
		return boogie2C.getTempvar2obj().containsKey(boogieId);
	}
	
	/**
	 * Translates Boogie identifiers of variables and functions back to 
	 * the identifiers of variables and operators in C.
	 * 
	 * This class is in an immature state and translates Strings to Strings.
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	public static class Boogie2C {
		
		private final Map<String,String> invar2cvar;
		private final Map<String,String> var2cvar;
		private final Map<String,Object> tempvar2obj;
		private final Map<String,String> functionId2operator;
		
		
		public Boogie2C() {
			super();
			this.invar2cvar = new HashMap<String,String>();
			this.var2cvar = new HashMap<String,String>();
			this.tempvar2obj = new HashMap<String,Object>();
			this.functionId2operator = new HashMap<String,String>();
		}


		public Map<String, String> getInvar2cvar() {
			return Collections.unmodifiableMap(invar2cvar);
		}


		public Map<String, String> getVar2cvar() {
			return Collections.unmodifiableMap(var2cvar);
		}


		public Map<String, Object> getTempvar2obj() {
			return Collections.unmodifiableMap(tempvar2obj);
		}


		public Map<String, String> getFunctionId2operator() {
			return Collections.unmodifiableMap(functionId2operator);
		}


		public void putFunction(String boogieId, String cId) {
			functionId2operator.put(boogieId, cId);
		}
		
		public void putVar(String boogieId, String cId) {
			var2cvar.put(boogieId, cId);
		}
		
		public void putInVar(String boogieId, String cId) {
			invar2cvar.put(boogieId, cId);
		}
		
		public void putTempVar(String boogieId, Object obj) {
			tempvar2obj.put(boogieId, obj);
		}
	}
}
