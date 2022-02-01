/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import static de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass.GLOBAL;
import static de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass.IMPLEMENTATION_INPARAM;
import static de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass.IMPLEMENTATION_OUTPARAM;
import static de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass.PROC_FUNC_INPARAM;
import static de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass.PROC_FUNC_OUTPARAM;
import static de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass.QUANTIFIED;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.VarMapKey;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.VarMapValue;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 * Part of @link {@link InlinerBacktranslator}.
 *
 * Still a work in progress, therefore no final comments.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ExpressionBacktranslation extends BoogieTransformer {

	private final Map<VarMapValue, VarMapKey> mReverseVarMap = new HashMap<>();

	private Set<String> mActiveProcedures = Collections.emptySet();

	private boolean mProcessedExprWasActive = false;

	public void reverseAndAddMapping(final Map<VarMapKey, VarMapValue> map) {
		for (final Map.Entry<VarMapKey, VarMapValue> entry : map.entrySet()) {
			final VarMapValue key = entry.getValue();
			final VarMapKey newValue = entry.getKey();
			final VarMapKey oldValue = mReverseVarMap.put(key, newValue);
			if (oldValue != null && !oldValue.equals(newValue)) {
				if (oldValue.getVarId().equals(oldValue.getVarId())) {
					final DeclarationInformation combinedDeclInfo =
							combineDeclInfo(oldValue.getDeclInfo(), newValue.getDeclInfo());
					final VarMapKey combinedValue = new VarMapKey(oldValue.getVarId(), combinedDeclInfo);
					mReverseVarMap.put(key, combinedValue);
				} else {
					throw new AssertionError("Ambiguous backtranslation mapping. Different variable names.");
				}
			}
		}
	}

	private static DeclarationInformation combineDeclInfo(final DeclarationInformation oldDI,
			final DeclarationInformation newDI) {
		final String oldProc = oldDI.getProcedure();
		final String newProc = newDI.getProcedure();
		if (oldProc != null && oldProc.equals(newProc) || oldProc == null && newProc == null) {
			final StorageClass oldSC = oldDI.getStorageClass();
			final StorageClass newSC = newDI.getStorageClass();
			if (oldSC == IMPLEMENTATION_INPARAM && newSC == PROC_FUNC_INPARAM
					|| newSC == IMPLEMENTATION_INPARAM && oldSC == PROC_FUNC_INPARAM) {
				return new DeclarationInformation(IMPLEMENTATION_INPARAM, oldProc);
			} else if (oldSC == IMPLEMENTATION_OUTPARAM && newSC == PROC_FUNC_OUTPARAM
					|| newSC == IMPLEMENTATION_OUTPARAM && oldSC == PROC_FUNC_OUTPARAM) {
				return new DeclarationInformation(IMPLEMENTATION_OUTPARAM, oldProc);
			} else {
				throw new AssertionError("Ambiguous translation mapping. DeclarationInformations cannot be merged: "
						+ oldDI + ", " + newDI);
			}
		}
		throw new AssertionError("Ambiguous translation mapping. Different procedure in DeclarationInformation: "
				+ oldDI + ", " + newDI);
	}

	/**
	 * Sets the set of procedures, whose variables are considered to be active.
	 * <p>
	 * A variable is active, if it isn't out of scope (like a local variable of procedure F, when the callstack doesn't
	 * contain F). Global variables and unknown variables (such without a mapping) are always considered to be active.
	 * <p>
	 * Calling this method will reset the intern <i>active</i> flag, used by {@link #processedExprWasActive()}.
	 *
	 * @param activeProcedures
	 *            {@link CallReinserter#unreturnedInlinedProcedures()}
	 */
	public void setInlinedActiveProcedures(final Set<String> activeProcedures) {
		mActiveProcedures = activeProcedures;
		mProcessedExprWasActive = false;
	}

	@Override
	public Expression processExpression(final Expression expr) {
		if (isDisguisedStruct(expr)) {
			return processDisguisedStruct((IdentifierExpression) expr);
		} else if (expr instanceof IdentifierExpression) {
			final IdentifierExpression idExpr = (IdentifierExpression) expr;
			final ILocation location = idExpr.getLocation();
			final IBoogieType type = idExpr.getType();
			final VarMapKey mapping =
					mReverseVarMap.get(new VarMapValue(idExpr.getIdentifier(), idExpr.getDeclarationInformation()));
			if (mapping == null) {
				mProcessedExprWasActive = true;
				return expr;
			}
			final DeclarationInformation translatedDeclInfo = mapping.getDeclInfo();
			final String translatedId = mapping.getVarId();
			Expression newExpr = new IdentifierExpression(location, type, translatedId, translatedDeclInfo);
			ModelUtils.copyAnnotations(expr, newExpr);
			if (mapping.getInOldExprOfProc() != null) {
				newExpr = new UnaryExpression(location, type, Operator.OLD, idExpr);
			}
			if (translatedDeclInfo.getStorageClass() == GLOBAL || translatedDeclInfo.getStorageClass() == QUANTIFIED
					|| mActiveProcedures.contains(translatedDeclInfo.getProcedure())) {
				mProcessedExprWasActive = true;
			}
			return newExpr;
		} else {
			return super.processExpression(expr);
		}
	}

	/**
	 * Recognizes IdentifierExpressions, which actually should be StructAcessExpressions.
	 * <p>
	 * This method is a workaround, since one would expect structs instead of simple variables. Eventually the
	 * preprocessor's backtranslation misses them.
	 *
	 * @param expr
	 *            Expression
	 * @return The Expression is an IdentifierExpression, which was created by the preprocessor to replace a
	 *         StructAccessExpression.
	 */
	private static boolean isDisguisedStruct(final Expression expr) {
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression idExpr = (IdentifierExpression) expr;
			return idExpr.getIdentifier().contains("!");
		}
		return false;
	}

	/**
	 * Backtranslates an IdentifierExpression, which actually should be an StructAcessExpression.
	 * <p>
	 * This method is a workaround, since one would expect structs instead of simple variables. Eventually the
	 * preprocessor's backtranslation misses them.
	 *
	 * @param disguisedStruct
	 *            IdentifierExpression from the preprocessor, which replaced a struct.
	 * @return Backtranslated struct as an IdentifierExpression.
	 */
	private IdentifierExpression processDisguisedStruct(final IdentifierExpression disguisedStruct) {
		final String[] idParts = disguisedStruct.getIdentifier().split("!", 2);
		assert idParts.length == 2 : "IdentifierExpression was no disguised struct: " + disguisedStruct;
		final IdentifierExpression struct = new IdentifierExpression(disguisedStruct.getLocation(), null, idParts[0],
				disguisedStruct.getDeclarationInformation());
		final IdentifierExpression newStruct = (IdentifierExpression) processExpression(struct);
		return new IdentifierExpression(newStruct.getLocation(), disguisedStruct.getType(),
				newStruct.getIdentifier() + "!" + idParts[1], newStruct.getDeclarationInformation());
	}

	/**
	 * Determines whether to keep processed variables in the ProgramState of an ProgramExecution or not.
	 * <p>
	 * A variable is active, if it isn't out of scope (like a local variable of procedure F, when the callstack doesn't
	 * contain F). Global variables and unknown variables (such without a mapping) are always considered to be active.
	 * <p>
	 * The returned value determines, that at least one of all processed variables was active. It is reseted with each
	 * call {@link #setInlinedActiveProcedures(Set)}.
	 *
	 * @return One of the processed expressions (since the last call of {@link #setInlinedActiveProcedures(Set)}) was
	 *         active.
	 */
	public boolean processedExprWasActive() {
		return mProcessedExprWasActive;
	}

}
