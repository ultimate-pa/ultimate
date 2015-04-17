package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.VarMapKey;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.VarMapValue;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

import static de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass.*;

/**
 * Part of @link {@link InlinerBacktranslator}.
 * 
 * Still a work in progress, therefore no final comments.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ExpressionBacktranslation extends BoogieTransformer {

	private Map<VarMapValue, VarMapKey> mReverseVarMap = new HashMap<>();

	public void reverseAndAddMapping(Map<VarMapKey, VarMapValue> map) {
		for (Map.Entry<VarMapKey, VarMapValue> entry : map.entrySet()) {
			VarMapValue key = entry.getValue();
			VarMapKey newValue = entry.getKey();
			VarMapKey oldValue = mReverseVarMap.put(key, newValue);
			if (oldValue != null && !oldValue.equals(newValue)) {
				if (oldValue.getVarId().equals(oldValue.getVarId())) {
					DeclarationInformation combinedDeclInfo = combineDeclInfo(oldValue.getDeclInfo(), newValue.getDeclInfo());
					VarMapKey combinedValue = new VarMapKey(oldValue.getVarId(), combinedDeclInfo);
					mReverseVarMap.put(key, combinedValue);
				} else {
					throw new AssertionError("Ambiguous backtranslation mapping. Different variable names.");
				}
			}
//			assert !criticalKeyCollision(prevValue, entry.getKey()) : ;
		}
	}
	
	private DeclarationInformation combineDeclInfo(DeclarationInformation oldDI, DeclarationInformation newDI) {
		String oldProc = oldDI.getProcedure();
		String newProc = newDI.getProcedure();
		if (oldProc != null && oldProc.equals(newProc) || oldProc == null && newProc == null) {
			StorageClass oldSC = oldDI.getStorageClass();
			StorageClass newSC = newDI.getStorageClass();
			if (oldSC == IMPLEMENTATION_INPARAM && newSC == PROC_FUNC_INPARAM
					|| newSC == IMPLEMENTATION_INPARAM && oldSC == PROC_FUNC_INPARAM) {
				return new DeclarationInformation(IMPLEMENTATION_INPARAM, oldProc);
			} else if (oldSC == IMPLEMENTATION_OUTPARAM && newSC == PROC_FUNC_OUTPARAM
					|| newSC == IMPLEMENTATION_OUTPARAM && oldSC == PROC_FUNC_OUTPARAM) {
				return new DeclarationInformation(IMPLEMENTATION_OUTPARAM, oldProc);
			} else {
				throw new AssertionError("Ambiguous backtranslation mapping. DeclarationInformations cannot be merged: "
						+ oldDI + ", " + newDI);
			}
		} else {
			throw new AssertionError("Ambiguous backtranslation mapping. Different declaration procedure: "
					+ oldDI + ", " + newDI);
		}
	}
	
//	private boolean criticalKeyCollision(VarMapKey prevValue, VarMapKey newValue) {
//		if (prevValue == null) {
//			return false;
//		}
//		return !prevValue.equals(newValue);
//	}

	@Override
	public Expression processExpression(Expression expr) {
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression idExpr = (IdentifierExpression) expr;
			ILocation location = idExpr.getLocation();
			IType type = idExpr.getType();
			VarMapKey mapping = mReverseVarMap.get(
					new VarMapValue(idExpr.getIdentifier(), idExpr.getDeclarationInformation()));
			if (mapping == null) {
				return expr;
			}
			DeclarationInformation translatedDeclInfo = mapping.getDeclInfo();
			String translatedId = mapping.getVarId();
			Expression newExpr = new IdentifierExpression(location, type, translatedId, translatedDeclInfo);
			ModelUtils.mergeAnnotations(expr, newExpr);
			if (mapping.getInOldExprOfProc() != null) {
				newExpr = new UnaryExpression(location, type, Operator.OLD, idExpr);
			}
			return newExpr;
		} else {
			return super.processExpression(expr);			
		}
	}

}
