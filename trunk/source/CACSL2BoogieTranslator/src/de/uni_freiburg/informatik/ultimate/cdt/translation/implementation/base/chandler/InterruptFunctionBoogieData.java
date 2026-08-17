/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE
 * CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE CACSL2BoogieTranslator plug-in,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE
 * CACSL2BoogieTranslator plug-in grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptServiceFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Holds all Boogie artifacts generated for a single {@link InterruptServiceFunction}.
 *
 * <p>
 * Each interrupt service routine gets its own enabled ghost variable, corresponding declaration, left-hand side, and
 * optional thread procedure. By encapsulating these artifacts per ISR, the {@link InterruptPostProcessor} can generate
 * them individually instead of maintaining a centralized map.
 * </p>
 *
 * @author Matthias Zumkeller
 */
public final class InterruptFunctionBoogieData {

	private static final ILocation IGNORE_LOC = LocationFactory.createIgnoreCLocation();

	private final InterruptServiceFunction mIsr;

	private final int mIrqNum;

	private final String mEnabledVarName;

	private final Expression mEnabledExpression;

	private final VariableDeclaration mEnabledDeclaration;

	private final VariableLHS mEnabledLhs;

	private Procedure mThreadProcedure;

	private InterruptFunctionBoogieData(final InterruptServiceFunction isr, final int irqNum,
			final String enabledVarName, final Expression enabledExpression, final VariableDeclaration enabledDeclaration,
			final VariableLHS enabledLhs) {
		mIsr = isr;
		mIrqNum = irqNum;
		mEnabledVarName = enabledVarName;
		mEnabledExpression = enabledExpression;
		mEnabledDeclaration = enabledDeclaration;
		mEnabledLhs = enabledLhs;
	}

	/**
	 * Constructs all Boogie artifacts for a single ISR.
	 *
	 * <p>
	 * This generates the enabled ghost variable named {@code #isr_<irqNum>_enabled} as a global boolean, along with its
	 * declaration and left-hand side.
	 * </p>
	 *
	 * @param isr
	 *            The interrupt service function.
	 * @return The constructed Boogie data for this ISR.
	 */
	public static InterruptFunctionBoogieData construct(final InterruptServiceFunction isr) {
		final int irqNum = isr.getIrqReference().getIrq().getNum();
		final String enabledVarName = constructEnabledVarName(irqNum);

		final Expression enabledExpression = ExpressionFactory.constructIdentifierExpression(IGNORE_LOC,
				BoogieType.TYPE_BOOL, enabledVarName, DeclarationInformation.DECLARATIONINFO_GLOBAL);

		final var astType = new PrimitiveType(IGNORE_LOC, "bool");
		final VariableDeclaration enabledDeclaration = new VariableDeclaration(IGNORE_LOC, new Attribute[0],
				new VarList[] { new VarList(IGNORE_LOC, new String[] { enabledVarName }, astType) });

		final VariableLHS enabledLhs = ExpressionFactory.constructVariableLHS(IGNORE_LOC, BoogieType.TYPE_BOOL,
				enabledVarName, DeclarationInformation.DECLARATIONINFO_GLOBAL);

		return new InterruptFunctionBoogieData(isr, irqNum, enabledVarName, enabledExpression, enabledDeclaration,
				enabledLhs);
	}

	/**
	 * Constructs the enabled variable name for a given IRQ number.
	 *
	 * @param irqNum
	 *            The IRQ number.
	 * @return The variable name {@code #isr_<irqNum>_enabled}.
	 */
	public static String constructEnabledVarName(final int irqNum) {
		return "#isr_" + irqNum + "_enabled";
	}

	/**
	 * Constructs the enabled expression for realization 2 (all ISRs in one thread).
	 *
	 * <p>
	 * Combines the ISR's enabled ghost variable with a non-deterministic boolean check: {@code enabled && havoc == 1}.
	 * </p>
	 *
	 * @param auxVarInfo
	 *            The auxiliary variable info for the non-deterministic boolean.
	 * @param expressionTranslation
	 *            The expression translation for constructing integer literals.
	 * @return The combined enabled expression.
	 */
	public Expression constructEnabledExpressionForRealization2(final AuxVarInfo auxVarInfo,
			final ExpressionTranslation expressionTranslation) {
		final CPrimitive cType = new CPrimitive(CPrimitives.BOOL);
		final Expression isOne = ExpressionFactory.newBinaryExpression(IGNORE_LOC, Operator.COMPEQ, auxVarInfo.getExp(),
				expressionTranslation.constructLiteralForIntegerType(IGNORE_LOC, cType, BigInteger.ONE));
		return ExpressionFactory.and(IGNORE_LOC, List.of(mEnabledExpression, isOne));
	}

	/**
	 * @return The ISR this data belongs to.
	 */
	public InterruptServiceFunction getIsr() {
		return mIsr;
	}

	/**
	 * @return The IRQ number of this ISR.
	 */
	public int getIrqNum() {
		return mIrqNum;
	}

	/**
	 * @return The name of the enabled ghost variable.
	 */
	public String getEnabledVarName() {
		return mEnabledVarName;
	}

	/**
	 * @return The enabled expression (identifier expression referencing the global boolean ghost variable).
	 */
	public Expression getEnabledExpression() {
		return mEnabledExpression;
	}

	/**
	 * @return The variable declaration for the enabled ghost variable.
	 */
	public VariableDeclaration getEnabledDeclaration() {
		return mEnabledDeclaration;
	}

	/**
	 * @return The left-hand side for assignments to the enabled ghost variable.
	 */
	public VariableLHS getEnabledLhs() {
		return mEnabledLhs;
	}

	/**
	 * @return The thread procedure for this ISR, or {@code null} if not yet set.
	 */
	public Procedure getThreadProcedure() {
		return mThreadProcedure;
	}

	/**
	 * Sets the thread procedure for this ISR.
	 *
	 * @param threadProcedure
	 *            The thread procedure.
	 */
	public void setThreadProcedure(final Procedure threadProcedure) {
		mThreadProcedure = threadProcedure;
	}

	/**
	 * Constructs the thread procedure name for this ISR.
	 *
	 * @return The thread name {@code #isr_<irqNum>_<procId>_thread}.
	 */
	public String constructThreadName() {
		return "#isr_" + mIrqNum + "_" + mIsr.getProcedure().getIdentifier() + "_thread";
	}
}
