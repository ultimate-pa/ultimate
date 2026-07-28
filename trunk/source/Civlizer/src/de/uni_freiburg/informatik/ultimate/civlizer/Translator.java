/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.civlizer.model.AnonymousAction;
import de.uni_freiburg.informatik.ultimate.civlizer.model.BoogieDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.CivlDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.CivlProgram;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration.Linearity;
import de.uni_freiburg.informatik.ultimate.civlizer.model.YieldInvariant;
import de.uni_freiburg.informatik.ultimate.civlizer.model.YieldProcedure;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;

/**
 * Translates an Ultimate Boogie AST and its associated proof annotations into a CIVL program representation and write
 * the result in a file.
 *
 * <p>
 * This class traverses the Boogie abstract syntax tree (AST), extracts thread information, invariants, ghost variables,
 * and proof annotations, and generates the corresponding Civl code as a file.
 * </p>
 *
 * <p>
 * The translation process includes:
 * <ul>
 * <li>Declaration of thread identifiers and auxiliary types.</li>
 * <li>Generation of ghost variables from Owicki-Gries proofs.</li>
 * <li>Creation of thread control-flow procedures (fork, join, terminate).</li>
 * <li>Translation of Boogie declarations and procedures.</li>
 * <li>Insertion of yield invariants derived from witness annotations.</li>
 * </ul>
 * </p>
 *
 * <p>
 * The resulting CIVL program is returned as a string and can be used for subsequent verification steps.
 * </p>
 *
 * @author Gabriel Tréca (gabriel.treca@polytechnique.edu)
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 */
public final class Translator {
	public static final int LAYER_BASE = 0;
	public static final int LAYER_IMPLEMENTATIONS = 1;
	public static final int LAYER_GHOST_VARS = 2;
	public static final int LAYER_TOP = LAYER_GHOST_VARS;

	private static final String JOIN_POOL_NAME = "join_pool";
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ProgramAndProof mProgramAndProof;
	private final VariablesInformation mVariablesInformation;

	private final ASTType mStartTidType;
	private final ASTType mTidType;

	private final List<CivlDeclaration> mDeclarations = new ArrayList<>();
	private final CivlProgram mResult;

	public Translator(final IUltimateServiceProvider services, final ProgramAndProof programAndProof) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		programAndProof.preprocess();
		mProgramAndProof = programAndProof;
		mVariablesInformation = new VariablesInformation(programAndProof);

		// Declarations for thread management operations
		mStartTidType = declareStartTidType();
		mTidType = addTidsType();
		addThreadControlFlow();

		declareGhostVariables();

		for (final Declaration elem : mProgramAndProof.getBoogieAst().getDeclarations()) {
			final var processedDecl = processDeclaration(elem);
			mDeclarations.add(processedDecl);
		}

		mResult = new CivlProgram(mDeclarations.toArray(CivlDeclaration[]::new));
	}

	ProgramAndProof getProgramAndProof() {
		// is used in body transformer
		return mProgramAndProof;
	}

	VariablesInformation getVariablesInformation() {
		return mVariablesInformation;
	}

	ASTType getStartTidType() {
		return mStartTidType;
	}

	ASTType getTidType() {
		return mTidType;
	}

	public CivlProgram getResult() {
		return mResult;
	}

	private void addTidConst(final Tid tid, final ASTType tidType) {
		final ILocation loc = null;
		final var tidConstDecl = new ConstDeclaration(loc, new Attribute[0], true,
				new VarList(loc, new String[] { "const_" + tid.toString() }, tidType), null, false);
		declare(tidConstDecl);
	}

	private void declare(final Declaration decl) {
		mDeclarations.add(new BoogieDeclaration(decl));
	}

	private ASTType declareStartTidType() {
		final ILocation loc = null;

		final var startTidType = new NamedType(loc, "StartTid", new ASTType[0]);
		final var startTidTypeDecl =
				new TypeDeclaration(loc, new Attribute[0], false, startTidType.getName(), new String[0]);
		declare(startTidTypeDecl);

		final var startTidConstDecl = new ConstDeclaration(loc, new Attribute[0], true,
				new VarList(loc, new String[] { "const_start_tid" }, startTidType), null, false);
		declare(startTidConstDecl);

		return startTidType;
	}

	private ASTType addTidsType() {
		final ILocation loc = null;

		final var tidType = new NamedType(loc, "Tid", new ASTType[0]);
		final var tidTypeDecl = new TypeDeclaration(loc, new Attribute[0], false, tidType.getName(), new String[0]);
		declare(tidTypeDecl);

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getTids()) {
			addTidConst(tid, tidType);
		}

		return tidType;
	}

	private void declareGhostVariables() {
		for (final OwickiGriesAnnotation proof : mProgramAndProof.getProof()) {
			for (int i = 0; i < proof.getGhostVariables().size(); i++) {
				// ??? TODO improve
				final var ghostDecl = createGlobalVariableDeclaration("~ghost~" + i, BoogieType.TYPE_INT,
						LAYER_GHOST_VARS, LAYER_TOP, false);
				declare(ghostDecl);
			}
		}
	}

	private static VariableDeclaration createGlobalVariableDeclaration(final String name, final BoogieType type,
			final int introductionLayer, final int disappearingLayer, final boolean linear) {
		final ILocation loc = null;

		final var layerAttribute = CivlUtils.createLayerAttribute(introductionLayer, disappearingLayer);
		final Attribute[] attributes;
		if (linear) {
			attributes = new Attribute[] { layerAttribute, CivlUtils.createLinearityAttribute(Linearity.INOUT) };
		} else {
			attributes = new Attribute[] { layerAttribute };
		}

		return new VariableDeclaration(loc, attributes,
				new VarList[] { new VarList(loc, new String[] { name }, type.toASTType(loc)) });
	}

	static ASTType makeOne(final ASTType innerType) {
		return new NamedType(null, "One", new ASTType[] { innerType });
	}

	// Creates the following yield procedure:
	//
	// yield procedure {:layer 0} fork_<procName>({:linear_in} tid : One Tid);
	// refines atomic action {:layer 1, 2} _ {}
	//
	private YieldProcedure addFork(final String procName) {
		final var tidParam = new ParameterDeclaration("tid", makeOne(mTidType), Linearity.IN);
		final var refinedAction = new AnonymousAction(LAYER_IMPLEMENTATIONS, LAYER_TOP,
				new Body(null, new VariableDeclaration[0], new Statement[0]));
		return new YieldProcedure(LAYER_BASE, "fork_" + procName, new ParameterDeclaration[] { tidParam },
				new ParameterDeclaration[0], new CallStatement[0], new CallStatement[0], null, refinedAction);
	}

	// Creates the following yield procedure:
	//
	// yield procedure {:layer 0} terminate({:linear_in} tid : One Tid);
	// refines atomic action {:layer 1, 2} _ {
	// call One_Put(join_pool, tid);
	// }
	//
	private YieldProcedure addTerminate() {
		final var tidParam = new ParameterDeclaration("tid", makeOne(mTidType), Linearity.IN);
		final var putCall = new CallStatement(null, new NamedAttribute[0], false, new VariableLHS[0], "One_Put",
				new Expression[] { getJoinPoolExpression(), getParameterExpression(tidParam) });
		final var refinedAction = new AnonymousAction(LAYER_IMPLEMENTATIONS, LAYER_TOP,
				new Body(null, new VariableDeclaration[0], new Statement[] { putCall }));
		return new YieldProcedure(LAYER_BASE, "terminate", new ParameterDeclaration[] { tidParam },
				new ParameterDeclaration[0], new CallStatement[0], new CallStatement[0], null, refinedAction);
	}

	// Creates the following yield procedure:
	//
	// yield procedure {:layer 0} join({:linear_out} tid : One Tid);
	// refines atomic action {:layer 1, 2} _ {
	// call One_Get(join_pool, tid);
	// }
	//
	private YieldProcedure addJoin() {
		final var tidParam = new ParameterDeclaration("tid", makeOne(mTidType), Linearity.OUT);

		final var setContain = new FunctionApplication(null, "Set_Contains",
				new Expression[] { getJoinPoolExpression(), getParameterExpression(tidParam) });

		final var assume = new AssumeStatement(null, setContain);
		final var getCall = new CallStatement(null, new NamedAttribute[0], false, new VariableLHS[0], "One_Get",
				new Expression[] { getJoinPoolExpression(), getParameterExpression(tidParam) });
		final var refinedAction = new AnonymousAction(LAYER_IMPLEMENTATIONS, LAYER_TOP,
				new Body(null, new VariableDeclaration[0], new Statement[] { assume, getCall }));
		return new YieldProcedure(LAYER_BASE, "join", new ParameterDeclaration[] { tidParam },
				new ParameterDeclaration[0], new CallStatement[0], new CallStatement[0], null, refinedAction);
	}

	private static Expression getJoinPoolExpression() {
		return new IdentifierExpression(null, JOIN_POOL_NAME);
	}

	private static Expression getParameterExpression(final ParameterDeclaration paramDecl) {
		return new IdentifierExpression(null, paramDecl.getIdentifier());
	}

	private void addThreadControlFlow() {
		final var joinPoolDecl = declareJoinPool();
		mDeclarations.add(new BoogieDeclaration(joinPoolDecl));

		for (final String procName : mProgramAndProof.getTemplateVisitor().getAssociationTidMap().keySet()) {
			final var forkDecl = addFork(procName);
			mDeclarations.add(forkDecl);
		}

		final var terminateDecl = addTerminate();
		mDeclarations.add(terminateDecl);

		final var joinDecl = addJoin();
		mDeclarations.add(joinDecl);
	}

	private VariableDeclaration declareJoinPool() {
		final var attributes = new Attribute[] { CivlUtils.createLayerAttribute(LAYER_BASE, LAYER_TOP),
				CivlUtils.createLinearityAttribute(Linearity.INOUT) };
		final ASTType poolType = new NamedType(null, "Set", new ASTType[] { makeOne(mTidType) });
		final var joinPoolDecl = new VariableDeclaration(null, attributes,
				new VarList[] { new VarList(null, new String[] { JOIN_POOL_NAME }, poolType) });
		return joinPoolDecl;
	}

	private CivlDeclaration processDeclaration(final Declaration decl) {
		return switch (decl) {
		case final Procedure proc -> processProcedure(proc);
		case final VariableDeclaration varDecl -> processGlobalVariableDeclaration(varDecl);

		// These declarations are passed through without changes.
		case final Axiom axiom -> new BoogieDeclaration(decl);
		case final ConstDeclaration constDecl -> new BoogieDeclaration(decl);
		case final FunctionDeclaration funDecl -> new BoogieDeclaration(decl);
		case final TypeDeclaration typeDecl -> new BoogieDeclaration(decl);
		};
	}

	// Add layer attribute to declaration of global program variables.
	private static CivlDeclaration processGlobalVariableDeclaration(final VariableDeclaration varDecl) {
		final var oldAttributes = varDecl.getAttributes();

		final var newAttributes = new Attribute[oldAttributes.length + 1];
		newAttributes[0] = CivlUtils.createLayerAttribute(LAYER_BASE, LAYER_TOP);
		System.arraycopy(oldAttributes, 0, newAttributes, 1, oldAttributes.length);

		final var newDecl = new VariableDeclaration(varDecl.getLoc(), newAttributes, varDecl.getVariables());
		return new BoogieDeclaration(newDecl);
	}

	CallStatement callYieldInvariants(final String procName, final int counter, final IdentifierExpression[] input,
			final Expression annotation) {
		// use to fix issue with addAll because Arrays.asList(input) return fix size
		final List<IdentifierExpression> params = new ArrayList<>(Arrays.asList(input));

		params.addAll(mVariablesInformation.getExpressionMap().getOrDefault(annotation, Collections.emptySet()));

		return new CallStatement(null, new NamedAttribute[0], false, new VariableLHS[0],
				"yield_" + procName + "_" + counter, params.toArray(Expression[]::new));
	}

	void addYieldInvariants(final String procName, final int counter, final Expression annotation,
			final Statement statement, final Set<Tid> tidNeedsLinearity) {
		final var params = new ArrayList<ParameterDeclaration>();
		if (BoogieUtils.START_PROCEDURE.equals(procName)) {
			params.add(new ParameterDeclaration("start_tid", makeOne(mStartTidType), Linearity.INOUT));
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			params.add(new ParameterDeclaration(tid.toString(), makeOne(mTidType),
					tidNeedsLinearity.contains(tid) ? Linearity.INOUT : Linearity.NONE));
		}

		for (final IdentifierExpression id : mVariablesInformation.getExpressionMap().getOrDefault(annotation,
				Collections.emptySet())) {
			// TODO maybe change type later
			final ASTType type = new NamedType(null, id.getType().toString(), new ASTType[0]);
			params.add(new ParameterDeclaration(id.getIdentifier(), type, Linearity.NONE));
		}

		final var preserves = new ArrayList<Expression>();
		if (BoogieUtils.START_PROCEDURE.equals(procName)) {
			preserves.add(new BinaryExpression(null, BinaryExpression.Operator.COMPEQ,
					new StructAccessExpression(null, new IdentifierExpression(null, "start_tid"), "val"),
					new IdentifierExpression(null, "const_start_tid")));
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			preserves.add(new BinaryExpression(null, BinaryExpression.Operator.COMPEQ,
					new StructAccessExpression(null, new IdentifierExpression(null, tid.toString()), "val"),
					new IdentifierExpression(null, "const_" + tid.toString())));
		}

		if (annotation != null) {
			preserves.add(annotation);
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			final Optional<String> forked_proc = mProgramAndProof.getTemplateVisitor().getAssociationTidMap().entrySet()
					.stream().filter(entry -> entry.getValue().contains(tid)).map(Map.Entry::getKey).findFirst();

			if (forked_proc.isPresent() && !procName.equals(forked_proc.get())) {
				// TODO set at the end of the procedure
				final var initialLoc = mProgramAndProof.getIcfg().getProcedureExitNodes().get(forked_proc.get());
				final var invariant = (Expression) WitnessInvariant.getAnnotation(initialLoc).getInvariant();

				preserves
						.add(new BinaryExpression(null, BinaryExpression.Operator.LOGICIMPLIES,
								new FunctionApplication(null, "Set_Contains", new Expression[] {
										getJoinPoolExpression(), new IdentifierExpression(null, tid.toString()) }),
								invariant));
			}
		}

		final var invDecl = new YieldInvariant(LAYER_TOP, "yield_" + procName + "_" + counter,
				params.toArray(ParameterDeclaration[]::new), preserves.toArray(Expression[]::new));
		mDeclarations.add(invDecl);
	}

	CallStatement callCondition(final String procName, final int counter, final Expression condition) {

		final List<IdentifierExpression> params = new ArrayList<>(
				mVariablesInformation.getExpressionMap().getOrDefault(condition, Collections.emptySet()));

		return new CallStatement(null, new NamedAttribute[0], false,
				new VariableLHS[] { new VariableLHS(null, "condition") }, "cond_" + procName + "_" + counter,
				params.toArray(IdentifierExpression[]::new));
	}

	// TODO add locality of parameter
	void addCondition(final String procName, final int counter, final Expression condition) {
		// maybe modify: new ParameterDeclaration("out", new PrimitiveType(null, "int"),
		// ParameterDeclaration.Linearity.NONE)

		final List<ParameterDeclaration> params = new ArrayList<>();

		for (final IdentifierExpression id : mVariablesInformation.getExpressionMap().getOrDefault(condition,
				Collections.emptySet())) {
			// TODO maybe change type later
			final ASTType type = new NamedType(null, id.getType().toString(), new ASTType[0]);
			params.add(new ParameterDeclaration(id.getIdentifier(), type, Linearity.NONE));
		}

		final var atomicAction = new AnonymousAction(LAYER_IMPLEMENTATIONS, LAYER_TOP,
				new Body(null, new VariableDeclaration[0], new Statement[] { new AssignmentStatement(null,
						new LeftHandSide[] { new VariableLHS(null, "out") }, new Expression[] { condition }) }));
		final var yieldProc = new YieldProcedure(LAYER_BASE, "cond_" + procName + "_" + counter,
				params.toArray(ParameterDeclaration[]::new),
				new ParameterDeclaration[] { new ParameterDeclaration("out", new PrimitiveType(null, "bool"),
						ParameterDeclaration.Linearity.NONE) },
				new CallStatement[0], new CallStatement[0], null, atomicAction);
		mDeclarations.add(yieldProc);
	}

	CallStatement callAtomicStatement(final String procName, final Statement statement, final int counter) {

		final List<Expression> inParams = new ArrayList<>();
		final List<VariableLHS> outParams = new ArrayList<>();

		for (final IdentifierExpression id : mVariablesInformation.getLocalStatementMap().getOrDefault(statement,
				Collections.emptySet())) {
			// TODO maybe change type later
			final ASTType type = new NamedType(null, id.getType().toString(), new ASTType[0]);
			inParams.add(id);
			outParams.add(new VariableLHS(null, id.getIdentifier()));
		}

		return new CallStatement(null, new NamedAttribute[0], false, outParams.toArray(VariableLHS[]::new),
				procName + "_stmt_" + counter, inParams.toArray(Expression[]::new));
	}

	private void addAtomicStatement(final String procName, final Statement statement, final int counter) {
		// IfStatement, ReturnStatement, CallStatement, WhileStatement, BreakStatement

		final List<ParameterDeclaration> inParams = new ArrayList<>();
		final List<ParameterDeclaration> outParams = new ArrayList<>();

		for (final IdentifierExpression id : mVariablesInformation.getLocalStatementMap().getOrDefault(statement,
				Collections.emptySet())) {
			// TODO maybe change type later
			final ASTType type = new NamedType(null, id.getType().toString(), new ASTType[0]);
			inParams.add(new ParameterDeclaration(id.getIdentifier() + "_in", type, Linearity.NONE));
			outParams.add(new ParameterDeclaration(id.getIdentifier(), type, Linearity.NONE));
		}

		final var body = new ArrayList<Statement>();
		// TODO improve this later
		for (final IdentifierExpression id : mVariablesInformation.getLocalStatementMap().getOrDefault(statement,
				Collections.emptySet())) {
			body.add(new AssignmentStatement(null, new LeftHandSide[] { new VariableLHS(null, id.getIdentifier()) },
					new Expression[] { new IdentifierExpression(null, id.getIdentifier() + "_in") }));
		}
		body.addAll(BoogieUtils.flattenAtomicStatements(statement));

		final var atomicAction = new AnonymousAction(LAYER_IMPLEMENTATIONS, LAYER_TOP,
				new Body(null, new VariableDeclaration[0], body.toArray(Statement[]::new)));
		final var yieldProc = new YieldProcedure(LAYER_BASE, procName + "_stmt_" + counter,
				inParams.toArray(ParameterDeclaration[]::new), outParams.toArray(ParameterDeclaration[]::new),
				new CallStatement[0], new CallStatement[0], null, atomicAction);
		mDeclarations.add(yieldProc);
	}

	void addStatement(final String procName, final Statement statement, final Set<Tid> tidNeedsLinearity,
			final int counter) {
		if (statement instanceof AssignmentStatement || statement instanceof AssertStatement
				|| statement instanceof AssumeStatement || statement instanceof HavocStatement
				|| statement instanceof AtomicStatement) {
			addAtomicStatement(procName, statement, counter);
		} else if (statement instanceof final IfStatement ifStmt) {
			addCondition(procName, counter, ifStmt.getCondition());
		} else if (statement instanceof final WhileStatement whileStmt) {
			addCondition(procName, counter, whileStmt.getCondition());
		}
	}

	Body writeBody(final Procedure decl) {
		final BodyTransformer transformer = new BodyTransformer(mServices, this);
		return transformer.transformBody(decl.getIdentifier(), decl.getBody());
	}

	// TODO could be reduce a lot core of what i need to get ride
	private YieldProcedure processProcedure(final Procedure decl) {

		// TODO declare the declaration with bodyTransformer

		final Set<Tid> tidNeedsLinearity = new HashSet<>(mProgramAndProof.getTemplateVisitor().getTids());

		final var inParams = new ArrayList<ParameterDeclaration>();

		if (BoogieUtils.START_PROCEDURE.equals(decl.getIdentifier())) {
			inParams.add(new ParameterDeclaration("start_tid", makeOne(mStartTidType), Linearity.INOUT));
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(decl.getIdentifier(),
				Collections.emptyList())) {
			inParams.add(new ParameterDeclaration(tid.toString(), makeOne(mTidType), Linearity.IN));
		}

		final Expression annotation =
				mProgramAndProof.getTemplateVisitor().getEntryAnnotationMap().get(decl.getIdentifier());
		addYieldInvariants(decl.getIdentifier(), 0, annotation, null, tidNeedsLinearity);

		final var requires = callYieldInvariants(decl.getIdentifier(), 0,
				inParams.stream().map(Translator::getParameterExpression).toArray(IdentifierExpression[]::new),
				annotation);

		final var body = writeBody(decl);
		return new YieldProcedure(LAYER_TOP, decl.getIdentifier(), inParams.toArray(ParameterDeclaration[]::new),
				new ParameterDeclaration[0], new CallStatement[] { requires }, new CallStatement[0], body, null);
	}
}
