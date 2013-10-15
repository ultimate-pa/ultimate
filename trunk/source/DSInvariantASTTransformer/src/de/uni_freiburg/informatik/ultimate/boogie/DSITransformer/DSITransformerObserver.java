package de.uni_freiburg.informatik.ultimate.boogie.DSITransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.DSITransformer.preferences.PreferenceValues;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

/**
 * This class transforms the procedures in the input AST into a single procedure
 * with a loop containing all the original procedures in order to generate data
 * structure invariants
 * 
 * @author arenis
 */
public final class DSITransformerObserver extends BoogieTransformer implements
		IUnmanagedObserver {

	/**
	 * Simply wraps the references to a procedure's declaration and
	 * implementation
	 * 
	 * @author arenis
	 * 
	 */
	private final class ProcedureContainer {
		public Procedure declaration = null, implementation = null;

		public Body getBody() {
			if (implementation != null)
				return implementation.getBody();
			return null;
		};

		public String getFilename() {
			if (declaration != null)
				return declaration.getLocation().getFileName();
			if (implementation != null)
				return implementation.getLocation().getFileName();
			return null;
		}

		public String getIdentifier() {
			if (declaration != null)
				return declaration.getIdentifier();
			if (implementation != null)
				return implementation.getIdentifier();
			return null;
		}

		public int getLineNr() {
			if (declaration != null)
				return declaration.getLocation().getStartLine();
			if (implementation != null)
				return implementation.getLocation().getStartLine();
			return 0;
		}
	}
	
	/**
	 * Looks recursively for the occurrence of $ptr(TYPE, PARM) in an
	 * expression. Given the type to look for and the list of parameters returns
	 * the identifier of the first parameter that matches this pattern. Call
	 * search(expr) to use, retrieve the name of the found parameter with
	 * getTheParm() if the search was successful
	 * 
	 * @author arenis
	 * 
	 */
	private final class PtrExpressionFinder extends BoogieTransformer {

		private String type;
		private boolean found;
		private Set<String> parms;
		private String theParm;

		public PtrExpressionFinder(String type, Set<String> parms) {
			this.type = type;
			this.parms = parms;
		}

		/**
		 * @return the Parameter found to be pointing to the type specified. May
		 *         be null if the parameter wasn't found.
		 */
		public String getTheParm() {
			return theParm;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer#processExpression(local
		 * .ultimate.model.boogie.ast.Expression)
		 */
		@Override
		protected Expression processExpression(Expression expr) {
			if (!found) {
				// We are looking for $ptr(type, some param)
				if (expr instanceof FunctionApplication) {
					FunctionApplication app = (FunctionApplication) expr;
					String name = app.getIdentifier();
					if (!name.equals("$ptr"))
						return super.processExpression(expr);
					Expression[] args = processExpressions(app.getArguments());
					if (args.length == 2
							&& args[0] instanceof IdentifierExpression
							&& args[1] instanceof IdentifierExpression) {
						IdentifierExpression left = (IdentifierExpression) args[0];
						IdentifierExpression right = (IdentifierExpression) args[1];
						if (left.getIdentifier().equals(type)
								&& parms.contains(right.getIdentifier())) {
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
		 * @return <code>true</code> if the pattern was found,
		 *         <code>false</code> otherwise
		 */
		public boolean search(Expression expr) {
			found = false;
			processExpression(expr);
			return found;
		}

	}
	
	private static final int PROC_NOT_VALID = 0;
	private static final int PROC_INITIALIZER = 1;
	private static final int PROC_MODIFIER = 2;

	/**
	 * String to be appended as suffix to the procedure name when generating
	 * labels
	 */
	private final String procPrefix = "_proc_";

	/**
	 * Output to console
	 */
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	/**
	 * Root of the newly created AST
	 */
	private WrapperNode root = null;

	/**
	 * List containing the procedures to be summarized
	 */
	private Map<String, ProcedureContainer> procedures;

	/**
	 * Signals when a procedure is being processed for variable renaming
	 */
	private boolean processingProcedure = false;

	/**
	 * Contains the prefix to be added to the local variable names of the
	 * procedure being processed
	 */
	private String procedureIDPrefix;

	/**
	 * A set containing the identifiers of the local variables for the procedure
	 * being processed
	 */
	private Map<String, String> procLocals;
	/**
	 * Label of the loop start (used at the exit of each procedure)
	 */
	private String procLoopStartLabel = "$DSInvariant_START";
	/**
	 * The type of the structure we want to investigate
	 */
	private String structureType = "^_TYPE";
	/**
	 * Identifier of the variable that represents the structure
	 */
	private String structureVarID = "$StructPTR";
	/**
	 * Enable to convert all assignments to $result into labels
	 */
	private boolean supressResultAssignments = false;
	/**
	 * Enable to trim the procedures after the last $wrap call this means also
	 * that a procedure without a $wrap call will not be considered
	 */
	private boolean trimAfterWrap = true;

	/**
	 * Label that marks the initialization section of the procedure
	 */
	private String procInitLabel = "$DSInvariant_INIT";
	/**
	 * Name of the procedure that gets created
	 */
	private String structureProcID = "$DSInvariant";

	/**
	 * Label for the exit of the loop
	 */
	private String procLoopEndLabel = "$DSInvariant_EXIT";

	/**
	 * TRUE if should just take all functions and put them in the loop. This is
	 * used for GUI Testing applications
	 */
	private boolean allFunctions = false;
	/**
	 * TRUE if the original procedure declarations should be left intact. They
	 * are otherwise removed when added to the loop structure.
	 */
	private boolean leaveOriginalProcedures = false;
	/**
	 * String that contains the exit label identifier for the procedure being
	 * processed. Only valid if processingProcedure == true
	 */
	private String procExitLabel;

	/**
	 * Counter to generate fresh labels
	 */
	private int procLabelCounter = 0;

	// @Override
	public void finish() {
	}

	/**
	 * 
	 * @return the root of the CFG.
	 */
	public INode getRoot() {
		return root;
	}

	// @Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	// @Override
	public void init() {
		s_Logger.info("Initializing DSITransformer...");
		procedures = new HashMap<String, ProcedureContainer>();

		// Retrieve settings from the Preferences Page
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.s_PLUGIN_ID);

		trimAfterWrap = prefs.getBoolean(PreferenceValues.NAME_TRIMWRAP,
				trimAfterWrap);

		structureType = prefs.get(PreferenceValues.NAME_STRUCTURETYPE,
				structureType);
		structureProcID = prefs.get(PreferenceValues.NAME_PROCEDUREID,
				structureProcID);
		allFunctions = prefs.getBoolean(PreferenceValues.NAME_ALLFUNCTIONS,
				PreferenceValues.VALUE_ALLFUNCTIONS_DEFAULT);
		leaveOriginalProcedures = prefs.getBoolean(
				PreferenceValues.NAME_LEAVEPROCEDURES,
				PreferenceValues.VALUE_LEAVEPROCEDURES);

		s_Logger.info("Generating procedure '" + structureProcID + "'.");

		if (!allFunctions) {
			s_Logger.info("Transforming for Data Structure '" + structureType
					+ "'.");

			String willTrim = "";
			if (!trimAfterWrap)
				willTrim = "NOT";
			s_Logger.info("Will " + willTrim + "trim procedures after $wrap.");

			String willLeave = "";
			if (leaveOriginalProcedures)
				willLeave = "NOT";
			s_Logger.info("Will " + willLeave
					+ "remove original procedure declarations.");
		} else
			s_Logger.info("Will process ALL procedures.");
	}

	@Override
	public boolean performedChanges() {
		return true;
	}

	/**
	 * Called by the Ultimate Framework. Receives the AST
	 */
	// @Override
	public boolean process(IElement root) {
		s_Logger.info("Scanning AST...");
		if (root instanceof WrapperNode) {
			if (((WrapperNode) root).getBacking() instanceof Unit) {
				Unit unit = (Unit) ((WrapperNode) root).getBacking();
				s_Logger.info("Unit found, processing declarations...");
				Unit newUnit = new Unit(null, null);
				this.root = new WrapperNode(null, newUnit);
				List<Declaration> newDeclarations = new ArrayList<Declaration>();

				boolean captured;
				for (Declaration d : unit.getDeclarations()) {
					captured = false;
					if (d instanceof Procedure) {
						// Select the interesting procedures and collect them in
						// a list: Procedures that have an implementation and
						// aren't part of the prelude
						Procedure proc = (Procedure) d;
						if (!proc.getIdentifier().startsWith("$")
								&& !proc.getIdentifier().contains("#")) {
							captured = true;
							ProcedureContainer pCont;
							if (procedures.containsKey(proc.getIdentifier()))
								pCont = procedures.get(proc.getIdentifier());
							else {
								pCont = new ProcedureContainer();
								procedures.put(proc.getIdentifier(), pCont);
							}

							if (proc.getBody() == null) {
								pCont.declaration = (Procedure) processDeclaration(proc);

								s_Logger.debug("Found procedure declaration: "
										+ proc.getIdentifier());
							} else {
								pCont.implementation = (Procedure) processDeclaration(proc);
								if (pCont.declaration == null)
									pCont.declaration = pCont.implementation;

								s_Logger
										.debug("Found procedure implementation: "
												+ proc.getIdentifier());
							}
						}
					}
					// Leave intact if directed to or if the declaration wasn't
					// captured for the loop.
					if (leaveOriginalProcedures || !captured)
						newDeclarations.add(super.processDeclaration(d));
				}
				// Process the collected procedures and add the newly created
				// one to our unit
				Procedure newProcedure = processProcedures();
				if (newProcedure != null) {
					if (allFunctions)
						newDeclarations.add(new FunctionDeclaration(null,
								new Attribute[] {}, "action", new String[] {},
								new VarList[] { new VarList(null,
										new String[] { "step" },
										new PrimitiveType(null, "int")) },
								new VarList(null, new String[] { "result" },
										new PrimitiveType(null, "int"))));

					newDeclarations.add(newProcedure);
				}
				newUnit.setDeclarations(newDeclarations
						.toArray(new Declaration[newDeclarations.size()]));

				s_Logger.info("Processed " + newUnit.getDeclarations().length
						+ " declarations.");
				return false;
			}
		}
		return true;
	}

	/*
	 * When a procedure is selected for processing, the local variables are
	 * renamed to make them unambiguous
	 * 
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer#processExpression(de.uni_freiburg.informatik.ultimate
	 * .model.boogie.ast.Expression)
	 */
	@Override
	protected Expression processExpression(Expression expr) {
		if (processingProcedure)
			if (expr instanceof IdentifierExpression) {
				IdentifierExpression e = (IdentifierExpression) expr;
				if (procLocals.containsKey(e.getIdentifier())) { // Only for
					// IdentifierExpressions
					// that are on the
					// list of locals
					IdentifierExpression result = new IdentifierExpression(null,
							e.getType(), procLocals.get(e.getIdentifier()));

					s_Logger.debug("Renamed in expression: "
							+ procLocals.get(e.getIdentifier()));
					return result;
				}
			}

		return super.processExpression(expr);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer#processLeftHandSide(local
	 * .ultimate.model.boogie.ast.LeftHandSide)
	 */
	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		if (!processingProcedure || lhs instanceof ArrayLHS
				|| !procLocals.containsKey(((VariableLHS) lhs).getIdentifier()))
			return super.processLeftHandSide(lhs);
		return new VariableLHS(null, procLocals.get(((VariableLHS) lhs)
				.getIdentifier()));
	}

	/**
	 * Transforms a procedure into a label, a set of assumes for the
	 * precondition, and the body statements with unambiguous variable names
	 * 
	 * @param p
	 *            The procedure to process
	 * @param vardecls
	 *            A list where the modified variable declarations will be
	 *            returned
	 * @param modifies
	 *            The set of identifiers corresponding to the Modifies clause to
	 *            be kept in the new method
	 * @param statements
	 *            A collection of Statements containing the processed procedure
	 *            body
	 * @return an integer representing the type of procedure identified
	 */
	private int processProcedure(ProcedureContainer p,
			Collection<VariableDeclaration> vardecls, Set<VariableLHS> modifies,
			Collection<Statement> statements) {

		procedureIDPrefix = p.getIdentifier() + "_";
		procExitLabel = structureProcID + "$" + procedureIDPrefix + "exit";
		VariableDeclaration[] locals = p.getBody().getLocalVars();

		// Create a set of Identifiers that will be renamed
		procLocals = new HashMap<String, String>();

		// Add the $result variable by default
		if (p.declaration.getOutParams().length > 0)
			procLocals.put("$result", procedureIDPrefix + "$result");
		// Add the locals
		for (VariableDeclaration vd : locals) {
			for (VarList vl : vd.getVariables()) {
				for (String v : vl.getIdentifiers()) {
					procLocals.put(v, procedureIDPrefix + v);
				}
			}
		}

		Set<String> parms = new HashSet<String>(
				p.declaration.getInParams().length);
		Map<String, String> parmCorrespondences = new HashMap<String, String>();
		// Include the in-parameters for the renaming
		int pIdx = 0;
		for (VarList pd : p.declaration.getInParams()) {
			int idIdx = 0;
			for (String parm : pd.getIdentifiers()) {
				parms.add(parm);
				procLocals.put(parm, procedureIDPrefix + parm);
				// Also rename the corresponding parameter in the implementation
				procLocals.put(p.implementation.getInParams()[pIdx]
						.getIdentifiers()[idIdx], procedureIDPrefix + parm);
				parmCorrespondences
						.put(parm, p.implementation.getInParams()[pIdx]
								.getIdentifiers()[idIdx]);
				idIdx++;
			}
			pIdx++;
		}

		// Look for the structure parameter
		// We'll know by looking for something in the form $ptr(Type, Parm)

		String theParm = null;
		PtrExpressionFinder finder = new PtrExpressionFinder(structureType,
				parms);
		for (Specification s : p.declaration.getSpecification()) {
			if (s instanceof RequiresSpecification
					|| s instanceof EnsuresSpecification) {
				Expression theSpec;
				if (s instanceof RequiresSpecification)
					theSpec = ((RequiresSpecification) s).getFormula();
				else
					theSpec = ((EnsuresSpecification) s).getFormula();
				finder.search(theSpec);
				if (finder.found) {
					theParm = finder.getTheParm();
					break;
				}
			}
		}

		if (!allFunctions)
			if (theParm != null) {
				procLocals.put(theParm, structureVarID);
				procLocals
						.put(parmCorrespondences.get(theParm), structureVarID);
				parms.remove(theParm); // Take it out of the list or else it
				// would
				// be declared again;
			} else
				return PROC_NOT_VALID;

		// Start the recursive processing with renaming
		processingProcedure = true;

		// Declare the renamed parameters
		VarList[] theLists = processVarLists(p.declaration.getInParams());
		ArrayList<VarList> newLists = new ArrayList<VarList>();
		for (VarList l : theLists) { // Filter the var. lists to remove the
			// pointer to the structure (avoid
			// multiple declaration)
			VarList newList;
			ArrayList<String> ids = new ArrayList<String>();
			for (String v : l.getIdentifiers()) {
				if (!v.equals(structureVarID))
					ids.add(v);
			}
			if (ids.size() > 0) {
				newList = new VarList(null, ids.toArray(new String[ids.size()]), l
						.getType());
				newLists.add(newList);
			}
		}

		ILocation loccationOfP = new BoogieLocation(p.getFilename(), p.getLineNr(), 
													-1, -1, -1, null);
		if (newLists.size() > 0) {
			vardecls.add(new VariableDeclaration(loccationOfP, 
					(Attribute[]) new NamedAttribute[0],
					newLists.toArray(new VarList[newLists.size()])));
		}

		// Create the list of the statements to be returned

		List<Statement> result = new ArrayList<Statement>();
		List<Statement> postConditions = new ArrayList<Statement>();

		// Havoc the parameters (except for the structure)
		if (parms.size() > 0) {
			VariableLHS[] parmsArray = new VariableLHS[parms.size()];
			int i = 0;
			for (String id : parms)
				parmsArray[i++] = new VariableLHS(loccationOfP, procedureIDPrefix + id);
			result.add(new HavocStatement(loccationOfP, parmsArray));
		}

		// Add the "modifies" specifications to the new method's specs.
		// Add the "requires" specifications as assume statements
		// Collect the "ensures" specifications as assert statements for the
		// end.
		for (Specification s : p.declaration.getSpecification()) {
			if (s instanceof ModifiesSpecification)
				for (VariableLHS id : ((ModifiesSpecification) s).getIdentifiers())
					modifies.add(id);
			else if (s instanceof RequiresSpecification) {
				AssumeStatement newAssume = new AssumeStatement(
						s.getLocation(),
						processExpression(((RequiresSpecification) s)
								.getFormula()));
				result.add(newAssume);
			} else if (s instanceof EnsuresSpecification) {
				if (!((EnsuresSpecification) s).isFree()) {
					AssertStatement newAssert = new AssertStatement(s
							.getLocation(),
							processExpression(((EnsuresSpecification) s)
									.getFormula()));
					postConditions.add(newAssert);
				}
			}
		}

		// Trigger processing (and thus renaming) and retrieve the modified body

		// First, the variable declarations
		Body newBody = processBody(p.getBody());

		for (VariableDeclaration var : newBody.getLocalVars())
			vardecls.add(var);

		// Add the declaration for the $result variable

		if (p.declaration.getOutParams().length > 0) {
			VarList[] resultList = new VarList[1];
			String[] resultStringList = { procedureIDPrefix + "$result" };
			resultList[0] = new VarList(null, resultStringList, p.declaration
					.getOutParams()[0].getType());
			vardecls.add(new VariableDeclaration(loccationOfP, 
												new Attribute[0], resultList));
		}

		Statement[] block = newBody.getBlock();

		int lastwrap = -1;
		int unwrap = -1;
		int i;

		// Add the statements
		for (i = 0; i < block.length; i++) {
			Statement s = block[i];
			result.add(s);
			// After each wrap a non-deterministic jump to the loop start
			// should be added
			if (s instanceof CallStatement
					&& (((CallStatement) s).getMethodName().equals("$wrap") || ((CallStatement) s)
							.getMethodName().equals("$static_wrap"))
					&& (((CallStatement) s).getArguments()[0]) instanceof FunctionApplication) {
				FunctionApplication fa = (FunctionApplication) (((CallStatement) s)
						.getArguments()[0]);
				if (fa.getArguments()[0] instanceof IdentifierExpression
						&& ((IdentifierExpression) fa.getArguments()[0])
								.getIdentifier().equals(structureType)) {
					if (unwrap > 0 && i > unwrap) { // Only do this if we saw an
						// unwrap before
						String newLabel = structureProcID + "$"
								+ Integer.toString(procLabelCounter++);
						result.add(new GotoStatement(null, new String[] {
								procLoopStartLabel, newLabel }));
						result.add(new Label(null, newLabel));
					}
					lastwrap = i;
				}
			} else if (s instanceof CallStatement
					&& (((CallStatement) s).getMethodName().equals("$unwrap") || ((CallStatement) s)
							.getMethodName().equals("$static_unwrap"))
					&& (((CallStatement) s).getArguments()[0]) instanceof FunctionApplication) {
				FunctionApplication fa = (FunctionApplication) (((CallStatement) s)
						.getArguments()[0]);
				if (fa.getArguments()[0] instanceof IdentifierExpression
						&& ((IdentifierExpression) fa.getArguments()[0])
								.getIdentifier().equals(structureType)) {
					unwrap = i;
				}
			}
		}

		// Add the exit label
		result.add(new Label(null, procExitLabel));
		// Add the postconditions as asserts
		result.addAll(postConditions);
		// Add the final jump to the loop head
		result
				.add(new GotoStatement(null, 
						new String[] { procLoopStartLabel }));

		// We're done with this procedure
		processingProcedure = false;

		statements.addAll(result);
		// If we found an unwrap, the procedure modifies the structure,
		// otherwise is considered an initializer
		if (unwrap < 0 && lastwrap >= 0)
			return PROC_INITIALIZER;
		return PROC_MODIFIER;
	}

	/**
	 * Processes the list of procedures and creates a new one that contains a
	 * loop with a non-deterministic jump to any of the bodies, the idea is to
	 * infer an invariant of this loop which would work as a data structure
	 * invariant.
	 * 
	 * @return A new procedure containing the loop structure.
	 */
	private Procedure processProcedures() {

		s_Logger.debug("Generating new procedure...");
		// List of the local Variable Declarations
		List<VariableDeclaration> procVars = new ArrayList<VariableDeclaration>();
		// List of the newly created procedure's statements
		List<Statement> statements = new ArrayList<Statement>();
		// List of Labels for each Procedure
		List<String> procLabels = new ArrayList<String>();
		// Set of the specifications to add to the new procedure
		Collection<Specification> procSpecs = new ArrayList<Specification>();
		// List of global variables modified by the new procedure
		Set<VariableLHS> procModifies = new HashSet<VariableLHS>();

		// List of the newly created procedure's initializing statements
		List<Statement> initStatements = new ArrayList<Statement>();
		// List of Labels for each initializer Procedure
		List<String> initLabels = new ArrayList<String>();

		int procCounter = 0;
		for (ProcedureContainer p : procedures.values()) { // Process each
			// procedure
			// individually
			if (p.getBody() == null)
				continue;

			Collection<VariableDeclaration> localVars = new ArrayList<VariableDeclaration>();
			Collection<Statement> localStatements = new ArrayList<Statement>();
			int procType;
			if ((procType = processProcedure(p, localVars, procModifies,
					localStatements)) != PROC_NOT_VALID) {

				Statement label = new Label(new BoogieLocation(p.getFilename(),-2,-2,-2,-2,null), procPrefix
						+ p.getIdentifier());
				// Add the label to the corresponding group
				if (allFunctions || procType == PROC_MODIFIER) {
					procLabels.add(procPrefix + p.getIdentifier());
					statements.add(label);
				} else {
					initLabels.add(procPrefix + p.getIdentifier());
					initStatements.add(label);
				}
				// Add the assume statement for the structure with the counter
				// function
				if (allFunctions)
					statements
							.add(new AssumeStatement(null, 
									new BinaryExpression(null,
											Operator.COMPEQ,
											new FunctionApplication(null,
													"action",
													new Expression[] { new IdentifierExpression(null,
															"$counter") }),
											new IntegerLiteral(null, Integer
													.toString(procCounter++)))));
				// Add the statements
				if (allFunctions || procType == PROC_MODIFIER) {
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
		if (!allFunctions)
			idArray = new String[] { structureVarID };
		else
			idArray = new String[] { structureVarID, "$counter" };
		VarList structPtr = new VarList(null, idArray, new PrimitiveType(null, "int"));
		// Careful, should be bound with a RealType
		VarList[] strPtrDecl;
		strPtrDecl = new VarList[] { structPtr };

		procVars.add(new VariableDeclaration(new BoogieLocation("",-5,-5,-5,-5,null),
				(Attribute[]) new NamedAttribute[0], strPtrDecl));

		// Now collect the statements in the right order
		List<Statement> procStatements = new ArrayList<Statement>();
		// Add the init label
		procStatements.add(new Label(new BoogieLocation("",-4,-4,-4,-4,null), procInitLabel));

		// Create the expression that represents the invariant
		// $inv($s, $ptr(THE_TYPE, structureVarID), THE_TYPE);

		Expression closedExp = new FunctionApplication(null, "$closed",
				new Expression[] {
						new IdentifierExpression(null, "$s"),
						new FunctionApplication(null, "$ptr", new Expression[] {
								new IdentifierExpression(null, structureType),
								new IdentifierExpression(null, structureVarID) }) });

		Expression ownerExp = new FunctionApplication(null, "$owner",
				new Expression[] {
						new IdentifierExpression(null, "$s"),
						new FunctionApplication(null, "$ptr", new Expression[] {
								new IdentifierExpression(null, structureType),
								new IdentifierExpression(null, structureVarID) }) });

		Expression ownedExp = new BinaryExpression(null, 
				BinaryExpression.Operator.COMPEQ, ownerExp,
				new FunctionApplication(null, "$me", new Expression[0]));

		Expression inv = new BinaryExpression(null, 
				BinaryExpression.Operator.LOGICAND, closedExp, ownedExp);

		if (!allFunctions) {
			if (initLabels.size() > 0) { // Add the initializer procedures
				GotoStatement initGoto = new GotoStatement(new BoogieLocation("",-3,-3,-3,-3,null), initLabels
						.toArray(new String[initLabels.size()]));
				procStatements.add(initGoto);
				procStatements.addAll(initStatements);
			} else
				procStatements.add(new AssumeStatement(null, inv));
		}

		// Add the start label
		procStatements.add(new Label(new BoogieLocation("",-4,-4,-4,-4,null), procLoopStartLabel));

		// Increment the counter (for the action(ctr))
		if (allFunctions)
			procStatements.add(new AssignmentStatement(null, 
					new LeftHandSide[] { new VariableLHS(null, "$counter") },
					new Expression[] { new BinaryExpression(null, 
							BinaryExpression.Operator.ARITHPLUS,
							new IdentifierExpression(null, "$counter"),
							new IntegerLiteral(null, "1")) }));

		// Add the invariant assertion (as loop invariant)
		// if (!allFunctions)
		// procStatements.add(new AssertStatement(null, null, inv));

		// Create the initial GOTO statement
		GotoStatement initGoto = new GotoStatement(new BoogieLocation("",-3,-3,-3,-3,null), procLabels
				.toArray(new String[procLabels.size()]));
		procStatements.add(initGoto);
		// Add the procedure bodies
		procStatements.addAll(statements);
		// Add the exit label
		procStatements.add(new Label(new BoogieLocation("",-4,-4,-4,-4,null), procLoopEndLabel));
		// Create the procedure's body
		Body procBody = new Body(null, procVars
				.toArray(new VariableDeclaration[procVars.size()]),
				procStatements.toArray(new Statement[statements.size()]));
		// Create the Modifies clause
		if (procModifies.size() > 0)
			procSpecs.add(new ModifiesSpecification(null, false, procModifies
					.toArray(new VariableLHS[procModifies.size()])));
		// Finally return the new procedure
		return new Procedure(new BoogieLocation("",-1,-1,-1,-1,null), new Attribute[0], structureProcID,
				new String[0], new VarList[0], new VarList[0], procSpecs
						.toArray(new Specification[procSpecs.size()]), procBody);
	}

	@Override
	protected Statement processStatement(Statement statement) {
		if (processingProcedure) {
			if (statement instanceof ReturnStatement) {
				String[] labels = { procExitLabel };
				return new GotoStatement(statement.getLocation(), labels);
			}
			if (statement instanceof Label) {
				return new Label(statement.getLocation(), procedureIDPrefix
								+ ((Label) statement).getName());
			}
			if (statement instanceof GotoStatement) {
				GotoStatement st = (GotoStatement) statement;
				String[] newlabels = new String[st.getLabels().length];
				for (int i = 0; i < newlabels.length; i++)
					newlabels[i] = procedureIDPrefix + st.getLabels()[i];
				return new GotoStatement(st.getLocation(),
						newlabels);
			}
			if (supressResultAssignments
					&& statement instanceof AssignmentStatement) {
				AssignmentStatement assign = (AssignmentStatement) statement;
				if (assign.getLhs()[0] instanceof VariableLHS) {
					VariableLHS var = (VariableLHS) assign.getLhs()[0];
					if (var.getIdentifier().equals("$result"))
						return new Label(statement.getLocation(), procedureIDPrefix
								+ Integer.toString(statement.getLocation().getStartLine()));
				}
			}
		}
		return super.processStatement(statement);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer#processVarList(de.uni_freiburg.informatik.ultimate
	 * .model.boogie.ast.VarList)
	 */
	@Override
	protected VarList processVarList(VarList vl) {
		if (processingProcedure) {
			boolean changed = false;
			ASTType type = vl.getType();
			ASTType newType = processType(type);
			Expression where = vl.getWhereClause();
			Expression newWhere = where != null ? processExpression(where)
					: null;
			String[] ids = vl.getIdentifiers(), newids = new String[ids.length];
			for (int i = 0; i < ids.length; i++) {
				if (procLocals.containsKey(ids[i])) {
					newids[i] = procLocals.get(ids[i]);

					s_Logger.debug("Renamed in declaration: " + newids[i]);
					changed = true;
				} else
					newids[i] = ids[i];
			}
			if (changed || newType != type || newWhere != where)
				return new VarList(null, newids, newType, newWhere);
			return vl;
		}
		return super.processVarList(vl);
	}
}
