/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Translation of the non-local jumps of C11 7.13 ({@code setjmp}/{@code longjmp}).
 * <p>
 * A {@code longjmp} is encoded as an exceptional return that is propagated through the callers by a ghost flag:
 * <ul>
 * <li>{@code setjmp(env)} at site k stores (k, activation id of the current procedure) for the pointer {@code env} in
 * two ghost maps, sets the ghost return value to 0 and is followed by an auxiliary label. Its value is read from the
 * ghost return value after the label.
 * <li>{@code longjmp(env, v)} sets the ghost flag {@link #PENDING}, copies the stored site and activation of
 * {@code env} into ghost variables, sets the ghost return value to {@code v} (or 1 if {@code v == 0}) and unwinds.
 * <li>Unwinding: if the flag is set and the target site belongs to the current activation, the flag is cleared and
 * control jumps to the label of the site (where the ghost return value becomes the value of {@code setjmp}),
 * otherwise the stack variables of the procedure are freed and the procedure returns. This unwinding code follows
 * every {@code longjmp} and every call of a C function.
 * <li>If the flag is still set when the entry function returns, the target activation was not alive any more
 * (undefined behavior), which is reported as unsupported feature.
 * </ul>
 * Local variables keep the values they had at the time of the {@code longjmp} (C11 7.13.2.1 makes non-volatile locals
 * that were changed indeterminate, we choose the value they have).
 * <p>
 * The pre-run collects the {@code setjmp} sites of every procedure and whether {@code longjmp} is used at all. The
 * main run only emits the encoding if {@code longjmp} is used, otherwise {@code setjmp} just returns 0.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public class SetjmpHandler {
	private static final String PENDING = "#ljmpPending";
	private static final String TARGET_SITE = "#ljmpSite";
	private static final String TARGET_FRAME = "#ljmpFrame";
	private static final String VALUE = "#ljmpVal";
	private static final String FRAME_COUNTER = "#ljmpFrameCounter";
	private static final String JMPBUF_SITE = "#jmpbufSite";
	private static final String JMPBUF_FRAME = "#jmpbufFrame";
	private static final String SELF_FRAME = "#ljmpFrame~self";
	private static final String LABEL_PREFIX = "SETJMP~";
	private static final CPrimitive GHOST_INT = new CPrimitive(CPrimitives.INT);

	private final ProcedureManager mProcedureManager;
	private final INameHandler mNameHandler;
	private final ITypeHandler mTypeHandler;
	private final StaticObjectsHandler mStaticObjectsHandler;
	private final MemoryHandler mMemoryHandler;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final boolean mIsPrerun;
	/**
	 * Pre-run: filled. Main run: the result of the pre-run.
	 */
	private final Map<String, List<IASTFunctionCallExpression>> mSitesOfProcedure;
	private boolean mUsesLongjmp;

	/**
	 * Main run only.
	 */
	private final Map<IASTFunctionCallExpression, Integer> mSiteIds;
	private final Map<IASTFunctionCallExpression, String> mSiteLabels;
	private final Set<IASTFunctionCallExpression> mTranslatedSites;
	private boolean mGlobalsDeclared;

	/**
	 * Constructor for the pre-run.
	 */
	public SetjmpHandler(final ProcedureManager procedureManager, final INameHandler nameHandler,
			final ITypeHandler typeHandler, final StaticObjectsHandler staticObjectsHandler,
			final MemoryHandler memoryHandler, final ExpressionTranslation expressionTranslation,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		this(true, new LinkedHashMap<>(), false, procedureManager, nameHandler, typeHandler, staticObjectsHandler,
				memoryHandler, expressionTranslation, auxVarInfoBuilder);
	}

	/**
	 * Constructor for the main run.
	 */
	public SetjmpHandler(final SetjmpHandler prerunHandler, final ProcedureManager procedureManager,
			final INameHandler nameHandler, final ITypeHandler typeHandler,
			final StaticObjectsHandler staticObjectsHandler, final MemoryHandler memoryHandler,
			final ExpressionTranslation expressionTranslation, final AuxVarInfoBuilder auxVarInfoBuilder) {
		this(false, prerunHandler.mSitesOfProcedure, prerunHandler.mUsesLongjmp, procedureManager, nameHandler,
				typeHandler, staticObjectsHandler, memoryHandler, expressionTranslation, auxVarInfoBuilder);
		if (!prerunHandler.mIsPrerun) {
			throw new IllegalArgumentException("Main-run SetjmpHandler needs the pre-run SetjmpHandler");
		}
	}

	private SetjmpHandler(final boolean isPrerun, final Map<String, List<IASTFunctionCallExpression>> sites,
			final boolean usesLongjmp, final ProcedureManager procedureManager, final INameHandler nameHandler,
			final ITypeHandler typeHandler, final StaticObjectsHandler staticObjectsHandler,
			final MemoryHandler memoryHandler, final ExpressionTranslation expressionTranslation,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		mIsPrerun = isPrerun;
		mSitesOfProcedure = sites;
		mUsesLongjmp = usesLongjmp;
		mProcedureManager = procedureManager;
		mNameHandler = nameHandler;
		mTypeHandler = typeHandler;
		mStaticObjectsHandler = staticObjectsHandler;
		mMemoryHandler = memoryHandler;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mSiteIds = new HashMap<>();
		mSiteLabels = new HashMap<>();
		mTranslatedSites = new HashSet<>();
		int id = 1;
		for (final List<IASTFunctionCallExpression> sitesOfProc : sites.values()) {
			for (final IASTFunctionCallExpression site : sitesOfProc) {
				mSiteIds.put(site, id);
				id++;
			}
		}
	}

	/**
	 * @return true iff the main run emits the longjmp encoding (i.e., the pre-run has seen a call to longjmp).
	 */
	public boolean isActive() {
		return !mIsPrerun && mUsesLongjmp;
	}

	/**
	 * Translate {@code setjmp(env)}.
	 *
	 * @param env
	 *            the translated argument (already converted to an RValue pointer)
	 */
	public ExpressionResult handleSetjmp(final ILocation loc, final IASTFunctionCallExpression node,
			final ExpressionResult env) {
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(env);
		if (mIsPrerun) {
			mSitesOfProcedure.computeIfAbsent(mProcedureManager.getCurrentProcedureID(), x -> new ArrayList<>())
					.add(node);
		}
		if (!isActive()) {
			// Without longjmp, setjmp only returns directly, i.e., 0.
			return builder.setLrValue(new RValue(
					mExpressionTranslation.constructLiteralForIntegerType(loc, intType, BigInteger.ZERO), intType))
					.build();
		}
		final String procedure = mProcedureManager.getCurrentProcedureID();
		final Integer siteId = mSiteIds.get(node);
		if (siteId == null || !mSitesOfProcedure.get(procedure).contains(node)) {
			throw new IllegalStateException("setjmp call at " + loc + " in " + procedure + " was not seen in pre-run");
		}
		if (!mTranslatedSites.add(node)) {
			throw new IllegalStateException("setjmp call at " + loc + " is translated twice, its label would be "
					+ "ambiguous");
		}
		declareGlobals(loc);
		final ILocation ignoreLoc = ghostLocation();
		final Expression envPtr = env.getLrValue().getValue();
		builder.addStatement(MemoryHandler.constructOneDimensionalArrayUpdate(ignoreLoc, envPtr,
				lhs(ignoreLoc, JMPBUF_SITE, jmpbufArrayType(), null), integer(ignoreLoc, siteId)));
		builder.addStatement(MemoryHandler.constructOneDimensionalArrayUpdate(ignoreLoc, envPtr,
				lhs(ignoreLoc, JMPBUF_FRAME, jmpbufArrayType(), null), selfFrame(ignoreLoc, procedure)));
		builder.addStatement(StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
				lhs(ignoreLoc, VALUE, ghostType(), null),
				mExpressionTranslation.constructLiteralForIntegerType(ignoreLoc, intType, BigInteger.ZERO)));
		builder.addStatement(BoogieUtils.constuctAuxiliaryLabel(ignoreLoc, getLabel(node)));
		final AuxVarInfo result = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType, SFO.AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(result);
		builder.addStatement(StatementFactory.constructSingleAssignmentStatement(ignoreLoc, result.getLhs(),
				id(ignoreLoc, VALUE, ghostType(), null)));
		return builder.setLrValue(new RValue(result.getExp(), intType)).build();
	}

	/**
	 * Translate {@code longjmp(env, val)}.
	 *
	 * @param env
	 *            the translated first argument (already converted to an RValue pointer)
	 * @param val
	 *            the translated second argument (already converted to an RValue of type int)
	 */
	public ExpressionResult handleLongjmp(final ILocation loc, final ExpressionResult env,
			final ExpressionResult val) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(env, val);
		if (mIsPrerun) {
			mUsesLongjmp = true;
			return builder.build();
		}
		if (!isActive()) {
			throw new IllegalStateException("longjmp at " + loc + " was not seen in pre-run");
		}
		declareGlobals(loc);
		final ILocation ignoreLoc = ghostLocation();
		final Expression envPtr = env.getLrValue().getValue();
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final Expression v = val.getLrValue().getValue();
		final Expression isZero = mExpressionTranslation.constructBinaryComparisonExpression(ignoreLoc,
				IASTBinaryExpression.op_equals, v, intType,
				mExpressionTranslation.constructLiteralForIntegerType(ignoreLoc, intType, BigInteger.ZERO), intType);
		final Expression value = ExpressionFactory.constructIfThenElseExpression(ignoreLoc, isZero,
				mExpressionTranslation.constructLiteralForIntegerType(ignoreLoc, intType, BigInteger.ONE), v);

		builder.addStatement(StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
				lhs(ignoreLoc, PENDING, BoogieType.TYPE_BOOL, null), ExpressionFactory.createBooleanLiteral(ignoreLoc,
						true)));
		builder.addStatement(StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
				lhs(ignoreLoc, TARGET_SITE, ghostType(), null), jmpbufAccess(ignoreLoc, JMPBUF_SITE, envPtr)));
		builder.addStatement(StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
				lhs(ignoreLoc, TARGET_FRAME, ghostType(), null),
				jmpbufAccess(ignoreLoc, JMPBUF_FRAME, envPtr)));
		builder.addStatement(StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
				lhs(ignoreLoc, VALUE, ghostType(), null), value));
		// the flag was just set, so we unwind without checking it
		builder.addStatements(constructUnwindingBody(loc));
		return builder.build();
	}

	/**
	 * @return The statements that follow a call of a C function in the current procedure: resume at a setjmp site of
	 *         the current activation or return, if a longjmp is pending. Empty if the encoding is not active.
	 */
	public List<Statement> constructUnwinding(final ILocation loc) {
		if (!isActive()) {
			return Collections.emptyList();
		}
		final ILocation ignoreLoc = ghostLocation();
		return List.of(new IfStatement(ignoreLoc, id(ignoreLoc, PENDING, BoogieType.TYPE_BOOL, null),
				constructUnwindingBody(loc).toArray(Statement[]::new), new Statement[0]));
	}

	/**
	 * @return The statements that propagate a pending longjmp: jump to a setjmp site of the current activation if it is
	 *         the target, otherwise free the stack variables and return.
	 */
	private List<Statement> constructUnwindingBody(final ILocation loc) {
		declareGlobals(loc);
		final ILocation ignoreLoc = ghostLocation();
		final String procedure = mProcedureManager.getCurrentProcedureID();
		final List<Statement> unwind = new ArrayList<>();
		for (final IASTFunctionCallExpression site : getSites(procedure)) {
			final Expression isTarget = ExpressionFactory.and(ignoreLoc,
					List.of(equals(ignoreLoc, id(ignoreLoc, TARGET_SITE, ghostType(), null),
							integer(ignoreLoc, mSiteIds.get(site))),
							equals(ignoreLoc, id(ignoreLoc, TARGET_FRAME, ghostType(), null),
									selfFrame(ignoreLoc, procedure))));
			final Statement[] resume = {
					StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
							lhs(ignoreLoc, PENDING, BoogieType.TYPE_BOOL, null),
							ExpressionFactory.createBooleanLiteral(ignoreLoc, false)),
					new GotoStatement(ignoreLoc, new String[] { getLabel(site) }) };
			unwind.add(new IfStatement(ignoreLoc, isTarget, resume, new Statement[0]));
		}
		// free the stack variables, as a return statement does
		for (final Entry<LocalLValueILocationPair, Integer> entry : mMemoryHandler.getVariablesToBeFreed()
				.entrySet()) {
			if (entry.getValue() >= 1) {
				unwind.add(mMemoryHandler.getDeallocCall(entry.getKey().llv(), entry.getKey().loc()));
				unwind.add(new HavocStatement(ignoreLoc,
						new VariableLHS[] { (VariableLHS) entry.getKey().llv().getLhs() }));
			}
		}
		unwind.add(new ReturnStatement(ignoreLoc));
		return unwind;
	}

	/**
	 * @return the declarations of locals that a procedure needs at its entry (its activation id).
	 */
	public List<VariableDeclaration> constructEntryDeclarations(final ILocation loc) {
		if (!isActive() || getSites(mProcedureManager.getCurrentProcedureID()).isEmpty()) {
			return Collections.emptyList();
		}
		final ILocation ignoreLoc = ghostLocation();
		return List.of(new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc, new String[] { SELF_FRAME }, ghostAstType(ignoreLoc)) }));
	}

	/**
	 * @return the statements that a procedure needs at its entry (fresh activation id, if it contains setjmp).
	 */
	public List<Statement> constructEntryStatements(final ILocation loc) {
		final String procedure = mProcedureManager.getCurrentProcedureID();
		if (!isActive() || getSites(procedure).isEmpty()) {
			return Collections.emptyList();
		}
		declareGlobals(loc);
		final ILocation ignoreLoc = ghostLocation();
		final Expression counter = id(ignoreLoc, FRAME_COUNTER, ghostType(), null);
		return List.of(
				StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
						lhs(ignoreLoc, SELF_FRAME, ghostType(), procedure), counter),
				StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
						lhs(ignoreLoc, FRAME_COUNTER, ghostType(), null),
						mExpressionTranslation.constructArithmeticExpression(ignoreLoc,
								IASTBinaryExpression.op_plus, counter, GHOST_INT, integer(ignoreLoc, 1), GHOST_INT)));
	}

	/**
	 * @return the statements that follow the call of the entry function: a longjmp that is still pending targets an
	 *         activation that is not alive any more (undefined behavior), which we do not support.
	 */
	public List<Statement> constructCheckAfterEntryFunction(final ILocation loc) {
		if (!isActive()) {
			return Collections.emptyList();
		}
		final ILocation ignoreLoc = ghostLocation();
		return List.of(new IfStatement(ignoreLoc, id(ignoreLoc, PENDING, BoogieType.TYPE_BOOL, null),
				new Statement[] { ExpressionTranslation.modelUnsupportedFeature(loc,
						"longjmp to a setjmp whose function has already returned") },
				new Statement[0]));
	}

	/**
	 * The ghost code gets a location without position. A position would be the one of the C call, and then waypoints
	 * of a witness (e.g., function_enter of that call) could be matched with the ghost code instead of the call.
	 */
	private static ILocation ghostLocation() {
		return LocationFactory.createIgnoreCLocation();
	}

	private List<IASTFunctionCallExpression> getSites(final String procedure) {
		return mSitesOfProcedure.getOrDefault(procedure, Collections.emptyList());
	}

	private String getLabel(final IASTFunctionCallExpression site) {
		return mSiteLabels.computeIfAbsent(site, x -> mNameHandler.getGloballyUniqueIdentifier(LABEL_PREFIX));
	}

	private void declareGlobals(final ILocation loc) {
		if (mGlobalsDeclared) {
			return;
		}
		mGlobalsDeclared = true;
		final ILocation ignoreLoc = ghostLocation();
		declareGlobal(ignoreLoc, PENDING, new PrimitiveType(ignoreLoc, BoogieType.TYPE_BOOL, SFO.BOOL));
		declareGlobal(ignoreLoc, TARGET_SITE, ghostAstType(ignoreLoc));
		declareGlobal(ignoreLoc, TARGET_FRAME, ghostAstType(ignoreLoc));
		declareGlobal(ignoreLoc, VALUE, ghostAstType(ignoreLoc));
		declareGlobal(ignoreLoc, FRAME_COUNTER, ghostAstType(ignoreLoc));
		final ASTType jmpbufType = new ArrayType(ignoreLoc, jmpbufArrayType(), new String[0],
				new ASTType[] { mTypeHandler.constructPointerType(ignoreLoc) }, ghostAstType(ignoreLoc));
		declareGlobal(ignoreLoc, JMPBUF_SITE, jmpbufType);
		declareGlobal(ignoreLoc, JMPBUF_FRAME, jmpbufType);
		mStaticObjectsHandler.addStatementsForUltimateInit(List.of(
				StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
						lhs(ignoreLoc, PENDING, BoogieType.TYPE_BOOL, null),
						ExpressionFactory.createBooleanLiteral(ignoreLoc, false)),
				StatementFactory.constructSingleAssignmentStatement(ignoreLoc,
						lhs(ignoreLoc, FRAME_COUNTER, ghostType(), null), integer(ignoreLoc, 0))));
	}

	private void declareGlobal(final ILocation loc, final String name, final ASTType type) {
		mStaticObjectsHandler.addGlobalVarDeclarationWithoutCDeclaration(new VariableDeclaration(loc,
				new Attribute[0], new VarList[] { new VarList(loc, new String[] { name }, type) }));
	}

	private Expression selfFrame(final ILocation loc, final String procedure) {
		return id(loc, SELF_FRAME, ghostType(), procedure);
	}

	private Expression jmpbufAccess(final ILocation loc, final String map, final Expression envPtr) {
		return ExpressionFactory.constructNestedArrayAccessExpression(loc, id(loc, map, jmpbufArrayType(), null),
				new Expression[] { envPtr });
	}

	private BoogieArrayType jmpbufArrayType() {
		return BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, ghostType());
	}

	/**
	 * Site ids and activation ids have the Boogie type of a C int (i.e., a bitvector in the bitvector translation,
	 * whose solvers might not support the sort Int).
	 */
	private BoogieType ghostType() {
		return mTypeHandler.getBoogieTypeForCType(GHOST_INT);
	}

	private ASTType ghostAstType(final ILocation loc) {
		return mTypeHandler.cType2AstType(loc, GHOST_INT);
	}

	private Expression integer(final ILocation loc, final int value) {
		return mExpressionTranslation.constructLiteralForIntegerType(loc, GHOST_INT, BigInteger.valueOf(value));
	}

	private Expression equals(final ILocation loc, final Expression left, final Expression right) {
		return mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_equals, left,
				GHOST_INT, right, GHOST_INT);
	}

	/**
	 * @param procedure
	 *            the procedure of a local variable, null for a global variable
	 */
	private static DeclarationInformation declInfo(final String procedure) {
		return procedure == null ? DeclarationInformation.DECLARATIONINFO_GLOBAL
				: new DeclarationInformation(StorageClass.LOCAL, procedure);
	}

	private static Expression id(final ILocation loc, final String name, final BoogieType type,
			final String procedure) {
		return ExpressionFactory.constructIdentifierExpression(loc, type, name, declInfo(procedure));
	}

	private static VariableLHS lhs(final ILocation loc, final String name, final BoogieType type,
			final String procedure) {
		return ExpressionFactory.constructVariableLHS(loc, type, name, declInfo(procedure));
	}
}
