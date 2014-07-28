package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Convert structured Boogie-Code (code containing while-loops, if-then-else constructs,
 * break statements) into unstructured Boogie-Code.  Unstructured Boogie-Code
 * is a sequence of Statements of the form:
 * <quote>(Label+ (Assert|Assume|Assign|Havoc|Call)*  (Goto|Return))+</quote>
 * In other words, a sequence of basic blocks, each starting with one or more labels 
 * followed by non-control statements and ended by a single Goto or Return statement. 
 * @author hoenicke
 *
 */
public class UnstructureCode implements IUnmanagedObserver {
	
	/** The prefix of automatically generated unique labels. */
	private static final String s_labelPrefix = "$Ultimate##";
	/** The list of unstructured statements of the procedure that were produced. */
	private LinkedList<Statement> m_flatStatements;
	/** A counter to produce unique label names. */
	int m_labelNr;
	/**
	 * True, iff the current statement is reachable.  This is set to false after a Return
	 * or Goto Statement was seen and to true if a label was just seen. 
	 */
	boolean m_reachable;
	/**
	 * This stack remembers for each named block the break info that maps the label of the
	 * break block to the destination label after the block.
	 */
	Stack<BreakInfo> m_breakStack;
	
	/**
	 * This class stores the information needed for breaking out of a block.  Whenever a break
	 * to breakLabel is found, it is replaced by a goto to destLabel.  If destLabel was not set
	 * at this time a new unique label is produced.  If after analyzing a block destLabel is 
	 * still not set, there is no break and the label does not need to be produced.
	 * @author hoenicke
	 *
	 */
	private static class BreakInfo {
		HashSet<String> breakLabels = new HashSet<String>();
		String destLabel;
		
		BreakInfo() {
		}
		
		void clear() {
			breakLabels.clear();
			destLabel = null;
		}
	}
	
	public BreakInfo findLabel(String label) {
		ListIterator<BreakInfo> it = m_breakStack.listIterator(m_breakStack.size());
		while (it.hasPrevious()) {
			BreakInfo bi = (BreakInfo) it.previous();
			if (bi.breakLabels.contains(label))
				return bi;
		}
		throw new TypeCheckException("Break to label "+label+" cannot be resolved.");
	}
	
	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter.
	 * This function descends to the unit node and then searches for all procedures and runs
	 * unstructureBody on it.
	 */
	public boolean process(IElement root) {
		if (root instanceof Unit) {
			Unit unit = (Unit) root;
			for (Declaration decl: unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					Procedure proc = (Procedure) decl;
					if (proc.getBody() != null)
						unstructureBody(proc);
				}
			}
			return false;
		}
		return true;
	}

	/**
	 * The main function that converts a body of a procedure into unstructured code.
	 */
	private void unstructureBody(Procedure proc) {
		Body body = proc.getBody();
		/* Initialize member variables */
		m_flatStatements = new LinkedList<Statement>();
		m_labelNr = 0;
		m_reachable = true;
		m_breakStack = new Stack<BreakInfo>();
		addLabel(new Label(proc.getLocation(), generateLabel()));
		
		/* Transform the procedure block */
		unstructureBlock(body.getBlock());
		
		/* If the last block doesn't have a goto or a return, add a return statement */
		// TODO Christian: add annotations? how?
		if (m_reachable)
			m_flatStatements.add(new ReturnStatement(proc.getLocation()));
		body.setBlock(m_flatStatements.toArray(new Statement[m_flatStatements.size()]));
	}
	
	private void addLabel(Label lab) {
		/* Check if we are inside a block and thus need to add a goto to this block */
	 // TODO Christian: add annotations? how?
		if (m_reachable && m_flatStatements.size() > 0
				&& !(m_flatStatements.getLast() instanceof Label)) {
			m_flatStatements.add
				(new GotoStatement(lab.getLocation(), 
						new String[] { lab.getName() }));
		}
		m_flatStatements.add(lab);
	}

	/**
	 * The recursive function that converts a block (i.e. a procedure block or while block or
	 * then/else-block) into unstructured code.
	 * @param block The sequence of statements in this block.
	 */
	private void unstructureBlock(Statement[] block) {
		/* The currentBI contains all labels of the current statement, and is used to generate
		 * appropriate break destination labels.
		 */ 
		BreakInfo currentBI = new BreakInfo();
		for (int i = 0; i < block.length; i++) {
			Statement s = block[i];
			if (s instanceof Label) {
				Label label = (Label) s;
				currentBI.breakLabels.add(label.getName());
				addLabel(label);
				m_reachable = true;
			} else {
				boolean reusedLabel = false;
				/* Hack: reuse label for breaks if possible */
				if (currentBI.destLabel == null && i+1 < block.length
						&& block[i+1] instanceof Label) {
					currentBI.destLabel = ((Label)block[i+1]).getName();
					reusedLabel = true;
				}
				m_breakStack.push(currentBI);
				unstructureStatement(currentBI, s);
				m_breakStack.pop();
				/* Create break label unless no break occurred or we reused existing label */
				if (!reusedLabel && currentBI.destLabel != null) {
					addLabel(new Label(s.getLocation(), currentBI.destLabel));
					m_reachable = true;
				}
				currentBI.clear();
			}
		}
	}

	private Expression getLHSExpression(LeftHandSide lhs) {
		Expression expr;
		if (lhs instanceof ArrayLHS) { 
			ArrayLHS arrlhs = (ArrayLHS) lhs;
			Expression array = getLHSExpression(arrlhs.getArray());
			expr = new ArrayAccessExpression(lhs.getLocation(), lhs.getType(), 
					array, arrlhs.getIndices());
		} else {
			VariableLHS varlhs = (VariableLHS) lhs;
			expr = new IdentifierExpression(lhs.getLocation(), lhs.getType(), 
					varlhs.getIdentifier(), varlhs.getDeclarationInformation());
		}
		return expr;
	}

	/**
	 * Converts a single statement to unstructured code.  This may produce many
	 * new flat statements for example if statement is a while-loop.
	 * @param outer  The BreakInfo of the current statement.  Used for if-then and
	 *  while which may implicitly jump to the end of the current statement.
	 * @param s  The current statement that should be converted (not a label).
	 */
	private void unstructureStatement(BreakInfo outer, Statement s) {
		if (s instanceof GotoStatement || s instanceof ReturnStatement) {
			m_flatStatements.add(s);
			m_reachable = false;			
		} else if (s instanceof BreakStatement) {
			String label = ((BreakStatement) s).getLabel();
			if (label == null)
				label = "*";
			BreakInfo dest = findLabel(label);
			if (dest.destLabel == null)
				dest.destLabel = generateLabel();
			addStmtAndAnnots(s, new GotoStatement(s.getLocation(),
			        new String[] {dest.destLabel}));
			m_reachable = false;
		} else if (s instanceof WhileStatement) {
			WhileStatement stmt = (WhileStatement) s;
			String head = generateLabel(); 
			String body = generateLabel();
			String done;
			
			if (! (stmt.getCondition() instanceof WildcardExpression))
				done = generateLabel();
			else {
				if (outer.destLabel == null)
					outer.destLabel = generateLabel();
				done = outer.destLabel;
			}
			
			//The label before the condition of the while loop gets the 
			// location that represents the while loop.
			ILocation loopLocation = new BoogieLocation(
					stmt.getLocation().getFileName(),
					stmt.getLocation().getStartLine(),
					stmt.getLocation().getEndLine(),
					stmt.getLocation().getStartColumn(),
					stmt.getLocation().getEndColumn(),
					stmt.getLocation().getOrigin(), true);
			addLabel(new Label(loopLocation, head));
			for (LoopInvariantSpecification spec : stmt.getInvariants()) {
				if (spec.isFree()) {
				    addStmtAndAnnots(s, new AssumeStatement(
                            spec.getLocation(), spec.getFormula()));
				} else {
				    addStmtAndAnnots(s, new AssertStatement(
                            spec.getLocation(), spec.getFormula()));
				}
			}
			addStmtAndAnnots(s, new GotoStatement(
                    s.getLocation(), new String[] {body, done}));
			addStmtAndAnnots(s, new Label(s.getLocation(), body));
			if (! (stmt.getCondition() instanceof WildcardExpression)) {
			    addStmtAndAnnots(s, new AssumeStatement(
                        stmt.getLocation(), stmt.getCondition()));
			}
			outer.breakLabels.add("*");
			unstructureBlock(stmt.getBody());
			if (m_reachable) {
			    addStmtAndAnnots(s, new GotoStatement(
			            s.getLocation(), new String[] { head }));
			}
			m_reachable = false;
			
			if (! (stmt.getCondition() instanceof WildcardExpression)) {
			    addStmtAndAnnots(s, new Label(s.getLocation(), done));
				addStmtAndAnnots(s, new AssumeStatement(stmt.getLocation(),
                        new UnaryExpression(stmt.getCondition().getLocation(),
                                BoogieType.boolType, UnaryExpression.Operator.LOGICNEG, 
                                stmt.getCondition())));
				m_reachable = true;
			}
		} else if (s instanceof IfStatement) {
			IfStatement stmt = (IfStatement) s;
			String thenLabel = generateLabel();
			String elseLabel = generateLabel();
			addStmtAndAnnots(s, new GotoStatement(stmt.getLocation(),
                    new String[] { thenLabel, elseLabel }));
			addStmtAndAnnots(s, new Label(s.getLocation(), thenLabel));
			if (! (stmt.getCondition() instanceof WildcardExpression)) {
			    addStmtAndAnnots(s, new AssumeStatement(stmt.getLocation(),
                        stmt.getCondition()));
			}
			unstructureBlock(stmt.getThenPart());
			if (m_reachable) {
				if (outer.destLabel == null)
					outer.destLabel = generateLabel();
				addStmtAndAnnots(s, new GotoStatement(
                        s.getLocation(), new String[] { outer.destLabel }));
			}
			m_reachable = true;
			addStmtAndAnnots(s, new Label(s.getLocation(), elseLabel));
			if (! (stmt.getCondition() instanceof WildcardExpression)) {
			    addStmtAndAnnots(s, new AssumeStatement(stmt.getLocation(),
                        new UnaryExpression(stmt.getCondition().getLocation(),
                                BoogieType.boolType,
                                UnaryExpression.Operator.LOGICNEG, 
                                stmt.getCondition())));
			}
			unstructureBlock(stmt.getElsePart());
		} else {
			if (s instanceof AssignmentStatement) {
				AssignmentStatement assign = (AssignmentStatement) s;
				LeftHandSide[] lhs = assign.getLhs();
				Expression[]   rhs = assign.getRhs();
				boolean changed = false;
				for (int i = 0; i < lhs.length; i++) {
					while (lhs[i] instanceof ArrayLHS) {
						LeftHandSide array = ((ArrayLHS) lhs[i]).getArray();
						Expression[] indices = ((ArrayLHS) lhs[i]).getIndices();
						Expression arrayExpr = (Expression) getLHSExpression(array);
						rhs[i] = new ArrayStoreExpression(lhs[i].getLocation(), 
								array.getType(), arrayExpr, indices, rhs[i]);
						lhs[i] = array;
						changed = true;
					}
				}
				if (changed)
					s = new AssignmentStatement(assign.getLocation(), lhs, rhs);
			}
			m_flatStatements.add(s);
		}
	}

	/**
	 * Adds a new statement to the list and also adds all annotations.
	 * 
	 * @param annotations annotations
	 * @param statement new statement to add
	 * @author Christian & Matthias
	 */
	private void addStmtAndAnnots(Statement sourceStmt, Statement newStmt) {
	    // adds annotations from old statement to new statement (if any)
	    BoogiePreprocessor.passAnnotations(sourceStmt, newStmt);
	    
	    // adds new statement to list
        m_flatStatements.add(newStmt);
    }

    private String generateLabel() {
		return s_labelPrefix + (m_labelNr++);
	}

	public void finish() {
	}

	public WalkerOptions getWalkerOptions() {
		return null;
	}

	public void init() {
	}

	@Override
	public boolean performedChanges() {
		// TODO Replace with a decent implementation!
		return getDefaultPerformedChanges();
	}

	@Deprecated
	private boolean getDefaultPerformedChanges() {
		return false;
	}
}
