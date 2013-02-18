package local.stalin.boogie.preprocessor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Stack;

import org.apache.log4j.Logger;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.boogie.type.BoogieType;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.boogie.ast.*;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;

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
	private static final Logger s_logger = StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/** The prefix of automatically generated unique labels. */
	private static final String s_labelPrefix = "$Stalin##";
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
		if (root instanceof WrapperNode) {
			Unit unit = (Unit) ((WrapperNode) root).getBacking();
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
		addLabel(new Label(proc.getFilename(), proc.getLineNr(), generateLabel()));
		
		/* Transform the procedure block */
		unstructureBlock(body.getBlock());
		
		/* If the last block doesn't have a goto or a return, add a return statement */
		if (m_reachable)
			m_flatStatements.add(new ReturnStatement("", 0));
		body.setBlock(m_flatStatements.toArray(new Statement[m_flatStatements.size()]));
	}
	
	private void addLabel(Label lab) {
		/* Check if we are inside a block and thus need to add a goto to this block */
		if (m_reachable && m_flatStatements.size() > 0
				&& !(m_flatStatements.getLast() instanceof Label)) {
			m_flatStatements.add
				(new GotoStatement(lab.getFilename(), lab.getLineNr(), 
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
			} else if (!m_reachable) {
				s_logger.warn(s.getFilename()+":"+s.getLineNr()+": Unreachable code.");
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
					addLabel(new Label(s.getFilename(), s.getLineNr(), currentBI.destLabel));
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
			expr = new ArrayAccessExpression(lhs.getType(), array, arrlhs.getIndices());
		} else {
			VariableLHS varlhs = (VariableLHS) lhs;
			expr = new IdentifierExpression(lhs.getType(), varlhs.getIdentifier());
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
			m_flatStatements.add(new GotoStatement(s.getFilename(), s.getLineNr(), 
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
			
			addLabel(new Label(s.getFilename(), s.getLineNr(), head));
			for (LoopInvariantSpecification spec : stmt.getInvariants()) {
				if (spec.isFree()) {
					m_flatStatements.add(
							new AssumeStatement(spec.getFilename(), spec.getLineNr(),
									spec.getFormula()));
				} else {
					m_flatStatements.add(
							new AssertStatement(spec.getFilename(), spec.getLineNr(),
									spec.getFormula()));
				}
			}
			m_flatStatements.add(new GotoStatement(s.getFilename(), s.getLineNr(), new String[] {body, done}));
			m_flatStatements.add(new Label(s.getFilename(), s.getLineNr(), body));
			if (! (stmt.getCondition() instanceof WildcardExpression))
				m_flatStatements.add(new AssumeStatement(stmt.getFilename(), stmt.getLineNr(),
						stmt.getCondition()));
			outer.breakLabels.add("*");
			unstructureBlock(stmt.getBody());
			if (m_reachable)
				m_flatStatements.add
					(new GotoStatement(s.getFilename(), s.getLineNr(), new String[] { head }));
			m_reachable = false;
			
			if (! (stmt.getCondition() instanceof WildcardExpression)) {
				m_flatStatements.add(new Label(s.getFilename(), s.getLineNr(), done));
				m_flatStatements.add(new AssumeStatement(stmt.getFilename(), stmt.getLineNr(),
						new UnaryExpression(BoogieType.boolType, UnaryExpression.Operator.LOGICNEG, 
								stmt.getCondition())));
				m_reachable = true;
			}
		} else if (s instanceof IfStatement) {
			IfStatement stmt = (IfStatement) s;
			String thenLabel = generateLabel();
			String elseLabel = generateLabel();
			m_flatStatements.add
			(new GotoStatement(stmt.getFilename(), stmt.getLineNr(), 
					new String[] { thenLabel, elseLabel }));
			m_flatStatements.add(new Label(s.getFilename(), s.getLineNr(), thenLabel));
			if (! (stmt.getCondition() instanceof WildcardExpression))
				m_flatStatements.add(new AssumeStatement(stmt.getFilename(), stmt.getLineNr(),
						stmt.getCondition()));
			unstructureBlock(stmt.getThenPart());
			if (m_reachable) {
				if (outer.destLabel == null)
					outer.destLabel = generateLabel();
				m_flatStatements.add
					(new GotoStatement(s.getFilename(), s.getLineNr(), new String[] { outer.destLabel }));
			}
			m_reachable = true;
			m_flatStatements.add(new Label(s.getFilename(), s.getLineNr(), elseLabel));
			if (! (stmt.getCondition() instanceof WildcardExpression))
				m_flatStatements.add(new AssumeStatement(stmt.getFilename(), stmt.getLineNr(),
						new UnaryExpression(BoogieType.boolType, UnaryExpression.Operator.LOGICNEG, 
								stmt.getCondition())));
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
						rhs[i] = new ArrayStoreExpression(array.getType(), arrayExpr, indices, rhs[i]);
						lhs[i] = array;
						changed = true;
					}
				}
				if (changed)
					s = new AssignmentStatement(assign.getFilename(), assign.getLineNr(), lhs, rhs);
			}
			m_flatStatements.add(s);
		}
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
