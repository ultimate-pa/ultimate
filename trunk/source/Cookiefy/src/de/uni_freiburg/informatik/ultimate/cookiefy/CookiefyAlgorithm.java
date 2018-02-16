/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jeremi Dzienian
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Cookiefy plug-in.
 *
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cookiefy.ContextPath.ContextPathNode;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Implementation of the Cookiefy Algorithm
 *
 * @author Jeremi
 */
public class CookiefyAlgorithm implements IUnmanagedObserver {

	/**
	 * Root of newly created AST
	 */
	private WrapperNode root = null;

	public IElement getRoot() {
		return root;
	}

	// public static ILogger logger =
	// UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	protected TemplateStore TemplateStore;
	protected Program InputProgram;
	private final ILogger mLogger;

	public CookiefyAlgorithm(final ILogger logger) {
		mLogger = logger;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		root = null;
	}

	@Override
	public void finish() {
		// cleanup
		InputProgram = null;
		TemplateStore = null;
	}

	@Override
	public boolean performedChanges() {
		// This algorithm creates a complete new AST
		return true;
	}

	@Override
	public boolean process(final IElement root) {

		if (root instanceof WrapperNode) {
			if (((WrapperNode) root).getBacking() instanceof Unit) {
				final Unit inputProgramUnit = (Unit) ((WrapperNode) root).getBacking();

				InputProgram = new Program(inputProgramUnit, mLogger);
				TemplateStore = new TemplateStore(InputProgram, mLogger);

				final Program EncodedProgram = Cookiefy(inputProgramUnit);
				if (EncodedProgram != null) {
					this.root = new WrapperNode(null, EncodedProgram.toUnit());
				}
				// do not traverse anymore
				return false;
			}
		}

		// traverse to next
		return true;
	}

	/**
	 * Executes the Cookiefy Algorithm
	 *
	 * @param P
	 *            input program
	 * @param entryPoint
	 *            main entry point of program (e.g. 'main')
	 * @param entryPointInit
	 *            parameters for entry Procedure
	 * @param globalVarsInit
	 *            initial valuation for global variables
	 * @return
	 */
	public Program Cookiefy(final Unit P, final String entryPoint, final Map<String, Expression> entryPointInit,
			final Map<String, Expression> globalVarsInit) {
		final Program EncodedProgram = new Program(mLogger);

		// add program entry point
		EncodedProgram.addProcedure(TemplateStore.programEntryPointTemplate("main", entryPointInit, globalVarsInit));

		EncodedProgram.Types.add(TemplateStore.bStackType);
		EncodedProgram.Types.add(TemplateStore.iStackType);
		EncodedProgram.Types.add(TemplateStore.iArrayType);

		// TODO: call a 'REAL" sub!
		mLogger.warn("Currently the Sub-Function is not implemented. Therefore we proceed with the following example temporal property:");
		mLogger.warn("AG(!foo)");

		for (final ContextPathNode cp : ContextPath.getAGNotFoo()) {
			EncodedProgram.addProcedure(TemplateStore.pReturn(cp.getPath()));
			for (final Procedure p : InputProgram.Procedures.values()) {
				// Alg: create procedure header (here postponed to end of loop)

				VarList[] newArg = new VarList[] {};
				if (cp.isAtom()) {
					newArg = TemplateStore.concatToEncParamsAtom(p);
				} else {
					newArg = TemplateStore.concatToEncParams(p);
				}
				// TODO: ensure, that no variable already named 'ret'! -> rename
				final VarList returnVar = new VarList(LocationProvider.getLocation(), new String[] { "ret" },
						new PrimitiveType(LocationProvider.getLocation(), "bool"));

				Statement[] statements = new Statement[0];
				if (cp.isTemporal()) {
					// OPTIMIZATION DONE:
					// At the beginning of the procedure: copy all parameters to
					// local vars, so they can be modified
					// This is not necessary in non temporal branches.
					statements = Helper.concatStatements(TemplateStore.cookifyArgsToVariables(p),
							TemporalProcedureBody(cp, p, EncodedProgram));
				} else {
					statements = TemplateStore.programFragmentTemplate(cp, p, 0);
				}

				// generate havoc procedure
				EncodedProgram.addProcedure(TemplateStore.encodeInitProcedurestateProcedure(p, cp.getPath(),
						new Expression[] {}));

				// create specifications (modifies)
				final List<Specification> specs = new LinkedList<Specification>();
				if (p.getOutParams().length > 0) {
					final String retValName = "retVal_" + ((PrimitiveType) p.getOutParams()[0].getType()).getName();
					final VariableLHS retVal = new VariableLHS(LocationProvider.getLocation(), retValName);
					specs.add(new ModifiesSpecification(LocationProvider.getLocation(), false,
							new VariableLHS[] { retVal }));
				}

				// create procedure
				EncodedProgram.addProcedure(new Procedure(LocationProvider.getLocation(), new Attribute[0],
						TemplateStore.methodeNameGen(p, cp.getPath(), ""), new String[0], newArg, // inParams
						new VarList[] { returnVar }, // outParams
						specs.toArray(new Specification[specs.size()]), new Body(LocationProvider
								.getLocation(), cp.isTemporal() // OPTIMIZATION
																// DONE
						? TemplateStore.cookifyArgsDeclareLocals(p, true, true)
								: new VariableDeclaration[0], statements)));
			}
		}

		// Add global (constructed) variables to encoded program
		create_globalRetVals(EncodedProgram);

		return EncodedProgram;
	}

	/**
	 * shortcut for Cookiefy Algorithm. Initializes some standard init values
	 *
	 * @param P
	 * @return
	 */
	public Program Cookiefy(final Unit P) {
		if (!InputProgram.Procedures.containsKey("main")) {
			mLogger.error("Input program contains no program entry point named 'main'");
			return null; // TODO??
		}

		// TODO: input program's parameters should be havoced here or should be
		// assigned a start value
		final HashMap<String, Expression> entryPointInit = new HashMap<String, Expression>();
		final HashMap<String, Expression> globalVarsInit = new HashMap<String, Expression>();

		return Cookiefy(P, "main", entryPointInit, globalVarsInit);
	}

	/**
	 * see algorithm 8 in "Cookiefy"
	 *
	 * @param cp
	 * @param p
	 * @param EncodedProgram
	 * @return
	 */
	private Statement[] TemporalProcedureBody(final ContextPathNode cp, final Procedure p, final Program EncodedProgram) {
		int pp = 0;
		final LinkedList<Statement> statements = new LinkedList<Statement>();

		for (final Statement s : p.getBody().getBlock()) {
			// handle call statements
			if (s instanceof CallStatement) {
				final CallStatement call = (CallStatement) s;
				pp++;
				// label
				statements.add(new Label(LocationProvider.getLocation(), String.format("$Cookiefy##%d", pp)));
				// template
				for (final Statement st : TemplateStore.programFragmentTemplate(cp, p, pp)) {
					statements.add(st);
				}
				// pcall
				statements.addAll(TemplateStore.stackPush(p, pp + 1));
				statements.add(TemplateStore.getHavocCallStatement(call.getArguments(),
						InputProgram.Procedures.get(((CallStatement) s).getMethodName()), cp.getPath()));
				statements.add(new ReturnStatement(LocationProvider.getLocation()));
				statements.add(new Label(LocationProvider.getLocation(), String.format("$Cookiefy##%d", ++pp)));
				// TODO catch value from preturn if more than one
				// catch return values
				if (call.getLhs().length > 1) {
					mLogger.warn("currently only 1-tuple returns supported in calls!");
				} else if (call.getLhs().length == 1) {
					// supports currently only one return value
					final ASTType retType = InputProgram.Procedures.get(call.getMethodName()).getOutParams()[0].getType();
					if (retType instanceof PrimitiveType) {
						final PrimitiveType ptype = (PrimitiveType) retType;
						final String globVarName = "retVal_" + ptype.getName();
						statements.add(new AssignmentStatement(LocationProvider.getLocation(),
								new LeftHandSide[] { call.getLhs()[0] }, new Expression[] { new IdentifierExpression(
										LocationProvider.getLocation(), globVarName) }));
					} else {
						mLogger.warn("currently only primitive data types supported as return value");
					}
				}
			}
			// handle return statements
			else if (s instanceof ReturnStatement) {
				pp++;
				statements.add(new Label(LocationProvider.getLocation(), String.format("$Cookiefy##%d", pp)));
				// Program Fragment Template
				for (final Statement st : TemplateStore.programFragmentTemplate(cp, p, pp)) {
					statements.add(st);
				}
				// (1) store return value into global variable retVal
				if (p.getOutParams().length > 0) {
					if (p.getOutParams()[0].getType() instanceof PrimitiveType) {

						// Fetch the return value
						final PrimitiveType ptype = (PrimitiveType) p.getOutParams()[0].getType();
						final String retValName = "retVal_" + ptype.getName();
						statements.add(new AssignmentStatement(LocationProvider.getLocation(),
								new LeftHandSide[] { new VariableLHS(LocationProvider.getLocation(), retValName) },
								new Expression[] { new IdentifierExpression(LocationProvider.getLocation(), p
										.getOutParams()[0].getIdentifiers()[0]) // TODO
																				// schoener!
								}));
					} else {
						mLogger.warn("currently only primitive data types supported!");
					}
				}
				// call the preturn
				if (!p.getIdentifier().equalsIgnoreCase("main")) {
					// SCPECIAL: the inputs program entry is not called by
					// another procedure! return normally
					statements.add(TemplateStore.pReturnCall(cp.getPath()));
				}
				statements.add(new ReturnStatement(LocationProvider.getLocation()));
			}
			// handle labels
			else if (s instanceof Label) {
				// OPTIMIZATION: input program labels must be
				// included, but no Cookiefy annotation is necessary:
				statements.add(s);
			}
			// all other statements
			else {
				pp++;
				// label
				statements.add(new Label(LocationProvider.getLocation(), String.format("$Cookiefy##%d", pp)));
				// template
				for (final Statement st : TemplateStore.programFragmentTemplate(cp, p, pp)) {
					statements.add(st);
				}
				// code
				statements.add(s);
			}
			// pp += 1; //increase procedure point (counter)
		}
		statements.add(new Label(LocationProvider.getLocation(), String.format("$Cookiefy##%d", ++pp)));

		// Insert gotos
		for (int i = 2; i <= pp; ++i) {
			statements.addFirst(new IfStatement(LocationProvider.getLocation(), new BinaryExpression(LocationProvider
					.getLocation(), Operator.COMPEQ, new IdentifierExpression(LocationProvider.getLocation(), "pp"),
					new IntegerLiteral(LocationProvider.getLocation(), String.format("%d", i))),
					new Statement[] { new GotoStatement(LocationProvider.getLocation(), new String[] { String.format(
							"$Cookiefy##%d", i) }) }, new Statement[0]));
		}

		return statements.toArray(new Statement[statements.size()]);
	}

	/**
	 * Create global return values for each type that could be returned
	 *
	 */
	private void create_globalRetVals(final Program encodedProgram) {
		final Map<String, VariableDeclaration> retVals = new HashMap<String, VariableDeclaration>();

		for (final Procedure p : TemplateStore.getInputProgram().Procedures.values()) {
			for (final VarList vl : p.getOutParams()) {
				if (vl.getType() instanceof PrimitiveType) {
					final PrimitiveType type = (PrimitiveType) vl.getType();
					if (retVals.containsKey(type.getName())) {
						// OPTIMIZATION DONE: only one retVal for each type
						continue;
					}
					retVals.put(type.getName(), new VariableDeclaration(LocationProvider.getLocation(),
							new Attribute[0], new VarList[] { new VarList(LocationProvider.getLocation(),
									new String[] { "retVal_" + type.getName() }, type) }));

				} else {
					mLogger.warn(String
							.format("Currently the generated stack handles only primitive types as return param! Affected procedure: %s type %s",
									p.getIdentifier(), vl.getType().toString()));
				}
			}
		}

		// add retVals to global Variables
		encodedProgram.Globals.addAll(retVals.values());
	}

}
