/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.03.2012
 */
public class NameHandler implements INameHandler {
	
	/**
	 * Local variables with similar identifiers may occur in different scopes.
	 * Since there are mainly two scopes in Boogie (global, local) we have to 
	 * make sure that every local C variables gets a unique name.
	 * The simple solution is to append the "compound counter" as a suffix to
	 * the Boogie variable.
	 * This has however a negative impact on the reproducibility (important for,
	 * e.g., the resue of automata). As soon as we add a new compound all 
	 * variables get different names.
	 * As an alternative we have a different solution in which we only use
	 * the compound counter to get a unique suffix for the variable.
	 * (We count the occurrences of id/compound counter pairs and use this as
	 * suffix.)   
	 */
	private static final boolean USE_COMPOUND_COUNTER_DIRECTLY_ASLOCAL_VAR_SUFFIX = false;
	private final NestedMap2<String, Integer, Integer> mLocalVarSuffix = new NestedMap2<>();

	/**
	 * Counter for temporary variables.
	 */
	private int mTmpUID;

	private int mGlobalCounter;

	private final CACSL2BoogieBacktranslator mBacktranslator;

	public NameHandler(final CACSL2BoogieBacktranslator backtranslator) {
		mBacktranslator = backtranslator;
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final Dispatcher main, final IASTNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use C handler for " + node.getClass());
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final Dispatcher main, final ACSLNode node) {
		throw new UnsupportedOperationException("Implementation error: Use ACSL handler for " + node.getClass());
	}

	@Override
	public String getUniqueIdentifier(final IASTNode scope, String cId, final int compCnt, final boolean isOnHeap, final CType cType) {
		if (cId.isEmpty()) {
			cId = getGloballyUniqueIdentifier("unnamed");
		}
		final String boogieId;
		{
			// special case struct field identifier
			// if some parent is IASTCompositeTypeSpecifier we need indentifier
			// for
			// field of struct, field of union, or constant of enum
			// we return the original name.
			IASTNode curr = scope; // TODO : is there a better way to do that?
			while (curr != null && !(curr.getParent() instanceof IASTTranslationUnit)) {
				if (curr instanceof IASTCompositeTypeSpecifier) {
					boogieId = cId;
					mBacktranslator.putVar(boogieId, cId, cType);
					return boogieId;
				}
				curr = curr.getParent();
			}
		}
		assert cId.length() > 0 : "Empty C identifier";
		assert (compCnt >= 0);
		// mark variables that we put on the heap manually (bc they are
		// addressoffed)
		// with a "#"
		String onHeapStr = "";
		if (isOnHeap) {
			onHeapStr = "#";
		}
		// add tilde to identifier and the compound counter if variable is not
		// used in the lowest compound nesting level (compCnt==0)
		if (compCnt > 0) {
			boogieId = "~" + onHeapStr + cId + "~" + generateUniqueLocalVarSuffix(cId, compCnt);
		} else {
			boogieId = "~" + onHeapStr + cId;
		}
		mBacktranslator.putVar(boogieId, cId, cType);
		return boogieId;
	}
	
	
	private int generateUniqueLocalVarSuffix(final String cId, final int compCnt) {
		if (USE_COMPOUND_COUNTER_DIRECTLY_ASLOCAL_VAR_SUFFIX) {
			return compCnt;
		} else {
			Integer result = mLocalVarSuffix.get(cId, compCnt);
			if (result == null) {
				final Map<Integer, Integer> map = mLocalVarSuffix.get(cId);
				if (map == null) {
					result = 0;
				} else {
					result = map.size();
				}
				mLocalVarSuffix.put(cId, compCnt, result);
			}
			return result;
		}
	}

	@Override
	public String getInParamIdentifier(final String cId, final CType cType) {
		// (alex:) in case of several unnamed parameters we need uniqueness
		// (still a little bit overkill, to make it precise we would need to
		// check whether
		// the current method has more than one unnamed parameter)
		final String boogieId = SFO.IN_PARAM + cId + (cId.isEmpty() ? mTmpUID++ : "");
		mBacktranslator.putInVar(boogieId, cId, cType);
		return boogieId;
	}

	@Override
	public String getTempVarUID(final SFO.AUXVAR purpose, final CType cType) {
		final String boogieId = SFO.TEMP + purpose.getId() + mTmpUID++;
		mBacktranslator.putTempVar(boogieId, purpose, cType);
		return boogieId;
	}

	@Override
	public String getGloballyUniqueIdentifier(final String looplabel) {
		return looplabel + mGlobalCounter++;
	}

	@Override
	public boolean isTempVar(final String boogieId) {
		return mBacktranslator.isTempVar(boogieId);
	}
}
