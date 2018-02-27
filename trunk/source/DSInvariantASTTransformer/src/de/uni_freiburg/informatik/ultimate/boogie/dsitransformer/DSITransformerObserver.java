/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Sergio Feo Arenis (arenis@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DSInvariantASTTransformer plug-in.
 * 
 * The ULTIMATE DSInvariantASTTransformer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DSInvariantASTTransformer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DSInvariantASTTransformer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DSInvariantASTTransformer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE DSInvariantASTTransformer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.dsitransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.dsitransformer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This class transforms the procedures in the input AST into a single procedure with a loop containing all the original
 * procedures in order to generate data structure invariants
 * 
 * @author arenis
 */
public final class DSITransformerObserver extends BoogieTransformer implements IUnmanagedObserver {

	private static final int PROC_NOT_VALID = 0;
	private static final int PROC_INITIALIZER = 1;
	private static final int PROC_MODIFIER = 2;

	/**
	 * String to be appended as suffix to the procedure name when generating labels
	 */
	private static final String PROCEDURE_PREFIX = "_proc_";

	/**
	 * Label of the loop start (used at the exit of each procedure)
	 */
	private static final String PROC_LOOP_START_LABEL = "$DSInvariant_START";

	/**
	 * Identifier of the variable that represents the structure
	 */
	private static final String STRUCTURE_VAR_ID = "$StructPTR";

	/**
	 * Label that marks the initialization section of the procedure
	 */
	private static final String PROC_INIT_LABEL = "$DSInvariant_INIT";

	/**
	 * Name of the procedure that gets created
	 */
	private String mStructureProcID = "$DSInvariant";

	/**
	 * The type of the structure we want to investigate
	 */
	private String mStructureType = "^_TYPE";

	/**
	 * Label for the exit of the loop
	 */
	private static final String procLoopEndLabel = "$DSInvariant_EXIT";

	/**
	 * Output to console
	 */
	private final ILogger mLogger;

	/**
	 * Root of the newly created AST
	 */
	private Unit mRoot;

	/**
	 * List containing the procedures to be summarized
	 */
	private Map<String, ProcedureContainer> mProcedures;

	/**
	 * Signals when a procedure is being processed for variable renaming
	 */
	private boolean mProcessingProcedure = false;

	/**
	 * Contains the prefix to be added to the local variable names of the procedure being processed
	 */
	private String procedureIDPrefix;

	/**
	 * A set containing the identifiers of the local variables for the procedure being processed
	 */
	private Map<String, String> procLocals;

	/**
	 * Enable to convert all assignments to $result into labels
	 */
	private final boolean mSupressResultAssignments = false;
	/**
	 * Enable to trim the procedures after the last $wrap call this means also that a procedure without a $wrap call
	 * will not be considered
	 */
	private boolean mTrimAfterWrap = true;

	/**
	 * TRUE if should just take all functions and put them in the loop. This is used for GUI Testing applications
	 */
	private boolean mAllFunctions = false;
	/**
	 * TRUE if the original procedure declarations should be left intact. They are otherwise removed when added to the
	 * loop structure.
	 */
	private boolean mLeaveOriginalProcedures = false;
	/**
	 * String that contains the exit label identifier for the procedure being processed. Only valid if
	 * processingProcedure == true
	 */
	private String mProcExitLabel;

	/**
	 * Counter to generate fresh labels
	 */
	private int mProcLabelCounter = 0;
	private final IUltimateServiceProvider mServices;

	public DSITransformerObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public void finish() {
		// no cleanup needed
	}

	/**
	 * 
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return mRoot;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mLogger.info("Initializing DSITransformer...");
		mProcedures = new HashMap<String, ProcedureContainer>();

		// Retrieve settings from the Preferences Page
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mTrimAfterWrap = prefs.getBoolean(PreferenceInitializer.LABEL_TRIMWRAP, mTrimAfterWrap);

		mStructureType = prefs.getString(PreferenceInitializer.LABEL_STRUCTURETYPE, mStructureType);
		mStructureProcID = prefs.getString(PreferenceInitializer.LABEL_PROCEDUREID, mStructureProcID);
		mAllFunctions = prefs.getBoolean(PreferenceInitializer.LABEL_ALLFUNCTIONS,
				PreferenceInitializer.VALUE_ALLFUNCTIONS_DEFAULT);
		mLeaveOriginalProcedures = prefs.getBoolean(PreferenceInitializer.LABEL_LEAVEPROCEDURES,
				PreferenceInitializer.VALUE_LEAVEPROCEDURES);

		mLogger.info("Generating procedure '" + mStructureProcID + "'.");

		if (!mAllFunctions) {
			mLogger.info("Transforming for Data Structure '" + mStructureType + "'.");

			String willTrim = "";
			if (!mTrimAfterWrap) {
				willTrim = "NOT";
			}
			mLogger.info("Will " + willTrim + "trim procedures after $wrap.");

			String willLeave = "";
			if (mLeaveOriginalProcedures) {
				willLeave = "NOT";
			}
			mLogger.info("Will " + willLeave + "remove original procedure declarations.");
		} else {
			mLogger.info("Will process ALL procedures.");
		}
	}

	@Override
	public boolean performedChanges() {
		return true;
	}

	/**
	 * Called by the Ultimate Framework. Receives the AST
	 */
	@Override
	public boolean process(final IElement root) {
		mLogger.info("Scanning AST...");
		if (root instanceof Unit) {

			final Unit unit = (Unit) root;
			mLogger.info("Unit found, processing declarations...");
			final Unit newUnit = new Unit(null, null);
			mRoot = newUnit;
			final List<Declaration> newDeclarations = new ArrayList<Declaration>();

			boolean captured;
			for (final Declaration d : unit.getDeclarations()) {
				captured = false;
				if (d instanceof Procedure) {
					// Select the interesting procedures and collect them in
					// a list: Procedures that have an implementation and
					// aren't part of the prelude
					final Procedure proc = (Procedure) d;
					if (!proc.getIdentifier().startsWith("$") && !proc.getIdentifier().contains("#")) {
						captured = true;
						ProcedureContainer pCont;
						if (mProcedures.containsKey(proc.getIdentifier())) {
							pCont = mProcedures.get(proc.getIdentifier());
						} else {
							pCont = new ProcedureContainer();
							mProcedures.put(proc.getIdentifier(), pCont);
						}

						if (proc.getBody() == null) {
							pCont.declaration = (Procedure) processDeclaration(proc);

							mLogger.debug("Found procedure declaration: " + proc.getIdentifier());
						} else {
							pCont.implementation = (Procedure) processDeclaration(proc);
							if (pCont.declaration == null) {
								pCont.declaration = pCont.implementation;
							}

							mLogger.debug("Found procedure implementation: " + proc.getIdentifier());
						}
					}
				}
				// Leave intact if directed to or if the declaration wasn't
				// captured for the loop.
				if (mLeaveOriginalProcedures || !captured) {
					newDeclarations.add(super.processDeclaration(d));
				}
			}
			// Process the collected procedures and add the newly created
			// one to our unit
			final Procedure newProcedure = processProcedures();
			if (newProcedure != null) {
				if (mAllFunctions) {
					newDeclarations
							.add(new FunctionDeclaration(null, new Attribute[] {}, "action", new String[] {},
									new VarList[] { new VarList(null, new String[] { "step" },
											new PrimitiveType(null, "int")) },
									new VarList(null, new String[] { "result" }, new PrimitiveType(null, "int"))));
				}

				newDeclarations.add(newProcedure);
			}
			newUnit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));

			mLogger.info("Processed " + newUnit.getDeclarations().length + " declarations.");
			return false;
		}

		return true;
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (mProcessingProcedure) {
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression e = (IdentifierExpression) expr;
				if (procLocals.containsKey(e.getIdentifier())) { // Only for
					// IdentifierExpressions
					// that are on the
					// list of locals
					final IdentifierExpression result = new IdentifierExpression(null, e.getType(),
							procLocals.get(e.getIdentifier()), e.getDeclarationInformation());
					ModelUtils.copyAnnotations(expr, result);

					mLogger.debug("Renamed in expression: " + procLocals.get(e.getIdentifier()));
					return result;
				}
			}
		}

		return super.processExpression(expr);
	}

	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		if (!mProcessingProcedure || lhs instanceof ArrayLHS
				|| !procLocals.containsKey(((VariableLHS) lhs).getIdentifier())) {
			return super.processLeftHandSide(lhs);
		}
		final VariableLHS newLhs = new VariableLHS(null, procLocals.get(((VariableLHS) lhs).getIdentifier()));
		ModelUtils.copyAnnotations(lhs, newLhs);
		return newLhs;
	}

	/**
	 * Transforms a procedure into a label, a set of assumes for the precondition, and the body statements with
	 * unambiguous variable names
	 * 
	 * @param p
	 *            The procedure to process
	 * @param vardecls
	 *            A list where the modified variable declarations will be returned
	 * @param modifies
	 *            The set of identifiers corresponding to the Modifies clause to be kept in the new method
	 * @param statements
	 *            A collection of Statements containing the processed procedure body
	 * @return an integer representing the type of procedure identified
	 */
	private int processProcedure(final ProcedureContainer p, final Collection<VariableDeclaration> vardecls,
			final Set<VariableLHS> modifies, final Collection<Statement> statements) {

		procedureIDPrefix = p.getIdentifier() + "_";
		mProcExitLabel = mStructureProcID + "$" + procedureIDPrefix + "exit";
		final VariableDeclaration[] locals = p.getBody().getLocalVars();

		// Create a set of Identifiers that will be renamed
		procLocals = new HashMap<String, String>();

		// Add the $result variable by default
		if (p.declaration.getOutParams().length > 0) {
			procLocals.put("$result", procedureIDPrefix + "$result");
		}
		// Add the locals
		for (final VariableDeclaration vd : locals) {
			for (final VarList vl : vd.getVariables()) {
				for (final String v : vl.getIdentifiers()) {
					procLocals.put(v, procedureIDPrefix + v);
				}
			}
		}

		final Set<String> parms = new HashSet<String>(p.declaration.getInParams().length);
		final Map<String, String> parmCorrespondences = new HashMap<String, String>();
		// Include the in-parameters for the renaming
		int pIdx = 0;
		for (final VarList pd : p.declaration.getInParams()) {
			int idIdx = 0;
			for (final String parm : pd.getIdentifiers()) {
				parms.add(parm);
				procLocals.put(parm, procedureIDPrefix + parm);
				// Also rename the corresponding parameter in the implementation
				procLocals.put(p.implementation.getInParams()[pIdx].getIdentifiers()[idIdx], procedureIDPrefix + parm);
				parmCorrespondences.put(parm, p.implementation.getInParams()[pIdx].getIdentifiers()[idIdx]);
				idIdx++;
			}
			pIdx++;
		}

		// Look for the structure parameter
		// We'll know by looking for something in the form $ptr(Type, Parm)

		String theParm = null;
		final PtrExpressionFinder finder = new PtrExpressionFinder(mStructureType, parms);
		for (final Specification s : p.declaration.getSpecification()) {
			if (s instanceof RequiresSpecification || s instanceof EnsuresSpecification) {
				Expression theSpec;
				if (s instanceof RequiresSpecification) {
					theSpec = ((RequiresSpecification) s).getFormula();
				} else {
					theSpec = ((EnsuresSpecification) s).getFormula();
				}
				finder.search(theSpec);
				if (finder.found) {
					theParm = finder.getTheParm();
					break;
				}
			}
		}

		if (!mAllFunctions) {
			if (theParm != null) {
				procLocals.put(theParm, STRUCTURE_VAR_ID);
				procLocals.put(parmCorrespondences.get(theParm), STRUCTURE_VAR_ID);
				parms.remove(theParm); // Take it out of the list or else it
				// would
				// be declared again;
			} else {
				return PROC_NOT_VALID;
			}
		}

		// Start the recursive processing with renaming
		mProcessingProcedure = true;

		// Declare the renamed parameters
		final VarList[] theLists = processVarLists(p.declaration.getInParams());
		final ArrayList<VarList> newLists = new ArrayList<VarList>();
		for (final VarList l : theLists) { // Filter the var. lists to remove the
			// pointer to the structure (avoid
			// multiple declaration)
			VarList newList;
			final ArrayList<String> ids = new ArrayList<String>();
			for (final String v : l.getIdentifiers()) {
				if (!v.equals(STRUCTURE_VAR_ID)) {
					ids.add(v);
				}
			}
			if (!ids.isEmpty()) {
				newList = new VarList(null, ids.toArray(new String[ids.size()]), l.getType());
				newLists.add(newList);
			}
		}

		final ILocation loccationOfP = new BoogieLocation(p.getFilename(), p.getLineNr(), -1, -1, -1);
		if (!newLists.isEmpty()) {
			vardecls.add(new VariableDeclaration(loccationOfP, new NamedAttribute[0],
					newLists.toArray(new VarList[newLists.size()])));
		}

		// Create the list of the statements to be returned

		final List<Statement> result = new ArrayList<Statement>();
		final List<Statement> postConditions = new ArrayList<Statement>();

		// Havoc the parameters (except for the structure)
		if (!parms.isEmpty()) {
			final VariableLHS[] parmsArray = new VariableLHS[parms.size()];
			int i = 0;
			for (final String id : parms) {
				parmsArray[i++] = new VariableLHS(loccationOfP, procedureIDPrefix + id);
			}
			result.add(new HavocStatement(loccationOfP, parmsArray));
		}

		// Add the "modifies" specifications to the new method's specs.
		// Add the "requires" specifications as assume statements
		// Collect the "ensures" specifications as assert statements for the
		// end.
		for (final Specification s : p.declaration.getSpecification()) {
			if (s instanceof ModifiesSpecification) {
				for (final VariableLHS id : ((ModifiesSpecification) s).getIdentifiers()) {
					modifies.add(id);
				}
			} else if (s instanceof RequiresSpecification) {
				final AssumeStatement newAssume = new AssumeStatement(s.getLocation(),
						processExpression(((RequiresSpecification) s).getFormula()));
				result.add(newAssume);
			} else if (s instanceof EnsuresSpecification) {
				if (!((EnsuresSpecification) s).isFree()) {
					final AssertStatement newAssert = new AssertStatement(s.getLocation(),
							processExpression(((EnsuresSpecification) s).getFormula()));
					postConditions.add(newAssert);
				}
			}
		}

		// Trigger processing (and thus renaming) and retrieve the modified body

		// First, the variable declarations
		final Body newBody = processBody(p.getBody());

		for (final VariableDeclaration var : newBody.getLocalVars()) {
			vardecls.add(var);
		}

		// Add the declaration for the $result variable

		if (p.declaration.getOutParams().length > 0) {
			final VarList[] resultList = new VarList[1];
			final String[] resultStringList = { procedureIDPrefix + "$result" };
			resultList[0] = new VarList(null, resultStringList, p.declaration.getOutParams()[0].getType());
			vardecls.add(new VariableDeclaration(loccationOfP, new Attribute[0], resultList));
		}

		final Statement[] block = newBody.getBlock();

		int lastwrap = -1;
		int unwrap = -1;
		int i;

		// Add the statements
		for (i = 0; i < block.length; i++) {
			final Statement s = block[i];
			result.add(s);
			// After each wrap a non-deterministic jump to the loop start
			// should be added
			if (s instanceof CallStatement
					&& (((CallStatement) s).getMethodName().equals("$wrap")
							|| ((CallStatement) s).getMethodName().equals("$static_wrap"))
					&& ((CallStatement) s).getArguments()[0] instanceof FunctionApplication) {
				final FunctionApplication fa = (FunctionApplication) ((CallStatement) s).getArguments()[0];
				if (fa.getArguments()[0] instanceof IdentifierExpression
						&& ((IdentifierExpression) fa.getArguments()[0]).getIdentifier().equals(mStructureType)) {
					if (unwrap > 0 && i > unwrap) { // Only do this if we saw an
						// unwrap before
						final String newLabel = mStructureProcID + "$" + Integer.toString(mProcLabelCounter++);
						result.add(new GotoStatement(null, new String[] { PROC_LOOP_START_LABEL, newLabel }));
						result.add(new Label(null, newLabel));
					}
					lastwrap = i;
				}
			} else if (s instanceof CallStatement
					&& (((CallStatement) s).getMethodName().equals("$unwrap")
							|| ((CallStatement) s).getMethodName().equals("$static_unwrap"))
					&& ((CallStatement) s).getArguments()[0] instanceof FunctionApplication) {
				final FunctionApplication fa = (FunctionApplication) ((CallStatement) s).getArguments()[0];
				if (fa.getArguments()[0] instanceof IdentifierExpression
						&& ((IdentifierExpression) fa.getArguments()[0]).getIdentifier().equals(mStructureType)) {
					unwrap = i;
				}
			}
		}

		// Add the exit label
		result.add(new Label(null, mProcExitLabel));
		// Add the postconditions as asserts
		result.addAll(postConditions);
		// Add the final jump to the loop head
		result.add(new GotoStatement(null, new String[] { PROC_LOOP_START_LABEL }));

		// We're done with this procedure
		mProcessingProcedure = false;

		statements.addAll(result);
		// If we found an unwrap, the procedure modifies the structure,
		// otherwise is considered an initializer
		if (unwrap < 0 && lastwrap >= 0) {
			return PROC_INITIALIZER;
		}
		return PROC_MODIFIER;
	}

	/**
	 * Processes the list of procedures and creates a new one that contains a loop with a non-deterministic jump to any
	 * of the bodies, the idea is to infer an invariant of this loop which would work as a data structure invariant.
	 * 
	 * @return A new procedure containing the loop structure.
	 */
	private Procedure processProcedures() {

		mLogger.debug("Generating new procedure...");
		// List of the local Variable Declarations
		final List<VariableDeclaration> procVars = new ArrayList<VariableDeclaration>();
		// List of the newly created procedure's statements
		final List<Statement> statements = new ArrayList<Statement>();
		// List of Labels for each Procedure
		final List<String> procLabels = new ArrayList<String>();
		// Set of the specifications to add to the new procedure
		final Collection<Specification> procSpecs = new ArrayList<Specification>();
		// List of global variables modified by the new procedure
		final Set<VariableLHS> procModifies = new HashSet<VariableLHS>();

		// List of the newly created procedure's initializing statements
		final List<Statement> initStatements = new ArrayList<Statement>();
		// List of Labels for each initializer Procedure
		final List<String> initLabels = new ArrayList<String>();

		int procCounter = 0;
		for (final ProcedureContainer p : mProcedures.values()) { // Process each
			// procedure
			// individually
			if (p.getBody() == null) {
				continue;
			}

			final Collection<VariableDeclaration> localVars = new ArrayList<VariableDeclaration>();
			final Collection<Statement> localStatements = new ArrayList<Statement>();
			int procType;
			if ((procType = processProcedure(p, localVars, procModifies, localStatements)) != PROC_NOT_VALID) {

				final Statement label = new Label(new BoogieLocation(p.getFilename(), -2, -2, -2, -2),
						PROCEDURE_PREFIX + p.getIdentifier());
				// Add the label to the corresponding group
				if (mAllFunctions || procType == PROC_MODIFIER) {
					procLabels.add(PROCEDURE_PREFIX + p.getIdentifier());
					statements.add(label);
				} else {
					initLabels.add(PROCEDURE_PREFIX + p.getIdentifier());
					initStatements.add(label);
				}
				// Add the assume statement for the structure with the counter
				// function
				if (mAllFunctions) {
					statements.add(new AssumeStatement(null,
							new BinaryExpression(null, Operator.COMPEQ,
									new FunctionApplication(null, "action",
											new Expression[] { new IdentifierExpression(null, "$counter") }),
									new IntegerLiteral(null, Integer.toString(procCounter++)))));
				}
				// Add the statements
				if (mAllFunctions || procType == PROC_MODIFIER) {
					statements.addAll(localStatements);
				} else {
					initStatements.addAll(localStatements);
				}
				procVars.addAll(localVars);
			}
		}

		procLabels.add(procLoopEndLabel);

		// Declare the pointer to the structure
		String[] idArray;
		if (!mAllFunctions) {
			idArray = new String[] { STRUCTURE_VAR_ID };
		} else {
			idArray = new String[] { STRUCTURE_VAR_ID, "$counter" };
		}
		final VarList structPtr = new VarList(null, idArray, new PrimitiveType(null, "int"));
		// Careful, should be bound with a RealType
		VarList[] strPtrDecl;
		strPtrDecl = new VarList[] { structPtr };

		procVars.add(new VariableDeclaration(new BoogieLocation("", -5, -5, -5, -5), new NamedAttribute[0],
				strPtrDecl));

		// Now collect the statements in the right order
		final List<Statement> procStatements = new ArrayList<Statement>();
		// Add the init label
		procStatements.add(new Label(new BoogieLocation("", -4, -4, -4, -4), PROC_INIT_LABEL));

		// Create the expression that represents the invariant
		// $inv($s, $ptr(THE_TYPE, structureVarID), THE_TYPE);

		final Expression closedExp = new FunctionApplication(null, "$closed",
				new Expression[] { new IdentifierExpression(null, "$s"),
						new FunctionApplication(null, "$ptr",
								new Expression[] { new IdentifierExpression(null, mStructureType),
										new IdentifierExpression(null, STRUCTURE_VAR_ID) }) });

		final Expression ownerExp = new FunctionApplication(null, "$owner",
				new Expression[] { new IdentifierExpression(null, "$s"),
						new FunctionApplication(null, "$ptr",
								new Expression[] { new IdentifierExpression(null, mStructureType),
										new IdentifierExpression(null, STRUCTURE_VAR_ID) }) });

		final Expression ownedExp = new BinaryExpression(null, BinaryExpression.Operator.COMPEQ, ownerExp,
				new FunctionApplication(null, "$me", new Expression[0]));

		final Expression inv = new BinaryExpression(null, BinaryExpression.Operator.LOGICAND, closedExp, ownedExp);

		if (!mAllFunctions) {
			if (!initLabels.isEmpty()) { // Add the initializer procedures
				final GotoStatement initGoto = new GotoStatement(new BoogieLocation("", -3, -3, -3, -3),
						initLabels.toArray(new String[initLabels.size()]));
				procStatements.add(initGoto);
				procStatements.addAll(initStatements);
			} else {
				procStatements.add(new AssumeStatement(null, inv));
			}
		}

		// Add the start label
		procStatements.add(new Label(new BoogieLocation("", -4, -4, -4, -4), PROC_LOOP_START_LABEL));

		// Increment the counter (for the action(ctr))
		if (mAllFunctions) {
			procStatements.add(new AssignmentStatement(null, new LeftHandSide[] { new VariableLHS(null, "$counter") },
					new Expression[] { new BinaryExpression(null, BinaryExpression.Operator.ARITHPLUS,
							new IdentifierExpression(null, "$counter"), new IntegerLiteral(null, "1")) }));
		}

		// Add the invariant assertion (as loop invariant)
		// if (!allFunctions)
		// procStatements.add(new AssertStatement(null, null, inv));

		// Create the initial GOTO statement
		final GotoStatement initGoto = new GotoStatement(new BoogieLocation("", -3, -3, -3, -3),
				procLabels.toArray(new String[procLabels.size()]));
		procStatements.add(initGoto);
		// Add the procedure bodies
		procStatements.addAll(statements);
		// Add the exit label
		procStatements.add(new Label(new BoogieLocation("", -4, -4, -4, -4), procLoopEndLabel));
		// Create the procedure's body
		final Body procBody = new Body(null, procVars.toArray(new VariableDeclaration[procVars.size()]),
				procStatements.toArray(new Statement[statements.size()]));
		// Create the Modifies clause
		if (!procModifies.isEmpty()) {
			procSpecs.add(
					new ModifiesSpecification(null, false, procModifies.toArray(new VariableLHS[procModifies.size()])));
		}
		// Finally return the new procedure
		return new Procedure(new BoogieLocation("", -1, -1, -1, -1), new Attribute[0], mStructureProcID,
				new String[0], new VarList[0], new VarList[0], procSpecs.toArray(new Specification[procSpecs.size()]),
				procBody);
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		if (mProcessingProcedure) {
			Statement newStatement = null;
			if (statement instanceof ReturnStatement) {
				final String[] labels = { mProcExitLabel };
				newStatement = new GotoStatement(statement.getLocation(), labels);
			}
			if (statement instanceof Label) {
				newStatement = new Label(statement.getLocation(), procedureIDPrefix + ((Label) statement).getName());
			}
			if (statement instanceof GotoStatement) {
				final GotoStatement st = (GotoStatement) statement;
				final String[] newlabels = new String[st.getLabels().length];
				for (int i = 0; i < newlabels.length; i++) {
					newlabels[i] = procedureIDPrefix + st.getLabels()[i];
				}
				newStatement = new GotoStatement(st.getLocation(), newlabels);
			}
			if (mSupressResultAssignments && statement instanceof AssignmentStatement) {
				final AssignmentStatement assign = (AssignmentStatement) statement;
				if (assign.getLhs()[0] instanceof VariableLHS) {
					final VariableLHS var = (VariableLHS) assign.getLhs()[0];
					if (var.getIdentifier().equals("$result")) {
						newStatement = new Label(statement.getLocation(),
								procedureIDPrefix + Integer.toString(statement.getLocation().getStartLine()));
					}
				}
			}
			if (newStatement != null) {
				ModelUtils.copyAnnotations(statement, newStatement);
				return newStatement;
			}
		}
		return super.processStatement(statement);
	}

	@Override
	protected VarList processVarList(final VarList vl) {
		if (mProcessingProcedure) {
			boolean changed = false;
			final ASTType type = vl.getType();
			final ASTType newType = processType(type);
			final Expression where = vl.getWhereClause();
			final Expression newWhere = where != null ? processExpression(where) : null;
			final String[] ids = vl.getIdentifiers(), newids = new String[ids.length];
			for (int i = 0; i < ids.length; i++) {
				if (procLocals.containsKey(ids[i])) {
					newids[i] = procLocals.get(ids[i]);

					mLogger.debug("Renamed in declaration: " + newids[i]);
					changed = true;
				} else {
					newids[i] = ids[i];
				}
			}
			if (changed || newType != type || newWhere != where) {
				final VarList newVl = new VarList(null, newids, newType, newWhere);
				ModelUtils.copyAnnotations(newVl, vl);
				return newVl;
			}
			return vl;
		}
		return super.processVarList(vl);
	}

	/**
	 * Simply wraps the references to a procedure's declaration and implementation
	 * 
	 * @author arenis
	 * 
	 */
	private final class ProcedureContainer {
		public Procedure declaration = null, implementation = null;

		public Body getBody() {
			if (implementation != null) {
				return implementation.getBody();
			}
			return null;
		};

		public String getFilename() {
			if (declaration != null) {
				return declaration.getLocation().getFileName();
			}
			if (implementation != null) {
				return implementation.getLocation().getFileName();
			}
			return null;
		}

		public String getIdentifier() {
			if (declaration != null) {
				return declaration.getIdentifier();
			}
			if (implementation != null) {
				return implementation.getIdentifier();
			}
			return null;
		}

		public int getLineNr() {
			if (declaration != null) {
				return declaration.getLocation().getStartLine();
			}
			if (implementation != null) {
				return implementation.getLocation().getStartLine();
			}
			return 0;
		}
	}

	/**
	 * Looks recursively for the occurrence of $ptr(TYPE, PARM) in an expression. Given the type to look for and the
	 * list of parameters returns the identifier of the first parameter that matches this pattern. Call search(expr) to
	 * use, retrieve the name of the found parameter with getTheParm() if the search was successful
	 * 
	 * @author arenis
	 * 
	 */
	private final class PtrExpressionFinder extends BoogieTransformer {

		private final String type;
		private boolean found;
		private final Set<String> parms;
		private String theParm;

		public PtrExpressionFinder(final String type, final Set<String> parms) {
			this.type = type;
			this.parms = parms;
		}

		/**
		 * @return the Parameter found to be pointing to the type specified. May be null if the parameter wasn't found.
		 */
		public String getTheParm() {
			return theParm;
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (!found) {
				// We are looking for $ptr(type, some param)
				if (expr instanceof FunctionApplication) {
					final FunctionApplication app = (FunctionApplication) expr;
					final String name = app.getIdentifier();
					if (!name.equals("$ptr")) {
						return super.processExpression(expr);
					}
					final Expression[] args = processExpressions(app.getArguments());
					if (args.length == 2 && args[0] instanceof IdentifierExpression
							&& args[1] instanceof IdentifierExpression) {
						final IdentifierExpression left = (IdentifierExpression) args[0];
						final IdentifierExpression right = (IdentifierExpression) args[1];
						if (left.getIdentifier().equals(type) && parms.contains(right.getIdentifier())) {
							found = true;
							theParm = right.getIdentifier();
							return expr;
						}
					}
				}
				return super.processExpression(expr);
			}
			return expr;
		}

		/**
		 * @param expr
		 *            The expression in which to search
		 * @return <code>true</code> if the pattern was found, <code>false</code> otherwise
		 */
		public boolean search(final Expression expr) {
			found = false;
			processExpression(expr);
			return found;
		}

	}
}
