/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation.LoopExitType;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 * Convert structured Boogie-Code (code containing while-loops, if-then-else constructs, break statements) into
 * unstructured Boogie-Code. Unstructured Boogie-Code is a sequence of Statements of the form: <quote>(Label+
 * (Assert|Assume|Assign|Havoc|Call)* (Goto|Return))+</quote> In other words, a sequence of basic blocks, each starting
 * with one or more labels followed by non-control statements and ended by a single Goto or Return statement.
 *
 * @author Jochen Hoenicke
 * @author Christian Schilling
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class UnstructureCode extends BaseObserver {

	/** The prefix of automatically generated unique labels. */
	private static final String sLabelPrefix = "$Ultimate##";
	/** The list of unstructured statements of the procedure that were produced. */
	private LinkedList<Statement> mFlatStatements;
	/** A counter to produce unique label names. */
	private int mLabelNr;
	/**
	 * True, iff the current statement is reachable. This is set to false after a Return or Goto Statement was seen and
	 * to true if a label was just seen.
	 */
	private boolean mReachable;
	/**
	 * This stack remembers for each named block the break info that maps the label of the break block to the
	 * destination label after the block.
	 */
	Stack<BreakInfo> mBreakStack;
	private final BoogiePreprocessorBacktranslator mTranslator;

	protected UnstructureCode(final BoogiePreprocessorBacktranslator translator) {
		mTranslator = translator;
	}

	public BreakInfo findLabel(final String label) {
		final ListIterator<BreakInfo> it = mBreakStack.listIterator(mBreakStack.size());
		while (it.hasPrevious()) {
			final BreakInfo bi = it.previous();
			if (bi.breakLabels.contains(label)) {
				return bi;
			}
		}
		throw new TypeCheckException("Break to label " + label + " cannot be resolved.");
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter. This function descends
	 * to the unit node and then searches for all procedures and runs unstructureBody on it.
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					final Procedure proc = (Procedure) decl;
					if (proc.getBody() != null) {
						unstructureBody(proc);
					}
				}
			}
			return false;
		}
		return true;
	}

	/**
	 * The main function that converts a body of a procedure into unstructured code.
	 */
	private void unstructureBody(final Procedure proc) {
		final Body body = proc.getBody();
		/* Initialize member variables */
		mFlatStatements = new LinkedList<>();
		mLabelNr = 0;
		mReachable = true;
		mBreakStack = new Stack<>();
		// TODO: Add label as "do not backtranslate"?
		addLabel(new Label(proc.getLocation(), generateLabel()));

		/* Transform the procedure block */
		unstructureBlock(body.getBlock());

		/*
		 * If the last block doesn't have a goto or a return, add a return statement
		 */
		// TODO Christian: add annotations? how?
		if (mReachable) {
			mFlatStatements.add(new ReturnStatement(proc.getLocation()));
		}
		body.setBlock(mFlatStatements.toArray(new Statement[mFlatStatements.size()]));
	}

	private void addLabel(final Label lab) {
		/*
		 * Check if we are inside a block and thus need to add a goto to this block
		 */
		if (mReachable && !mFlatStatements.isEmpty() && !(mFlatStatements.getLast() instanceof Label)) {
			final GotoStatement gotoStmt = new GotoStatement(lab.getLocation(), new String[] { lab.getName() });
			ModelUtils.copyAnnotations(lab, gotoStmt);
			mFlatStatements.add(gotoStmt);
		}
		mFlatStatements.add(lab);
	}

	/**
	 * The recursive function that converts a block (i.e. a procedure block or while block or then/else-block) into
	 * unstructured code.
	 *
	 * @param block
	 *            The sequence of statements in this block.
	 */
	private void unstructureBlock(final Statement[] block) {
		/*
		 * The currentBI contains all labels of the current statement, and is used to generate appropriate break
		 * destination labels.
		 */
		final BreakInfo currentBI = new BreakInfo();
		for (int i = 0; i < block.length; i++) {
			final Statement s = block[i];
			if (s instanceof Label) {
				final Label label = (Label) s;
				if (label.getName().startsWith(sLabelPrefix)) {
					// FIXME: report unsupported syntax instead
					throw new AssertionError("labels with prefix " + sLabelPrefix
							+ " are reseved for auxiliary labels and are disallowed in input ");
				}
				currentBI.breakLabels.add(label.getName());
				addLabel(label);
				mReachable = true;
			} else {
				boolean reusedLabel = false;
				/* Hack: reuse label for breaks if possible */
				if (currentBI.destLabel == null && i + 1 < block.length && block[i + 1] instanceof Label) {
					currentBI.destLabel = ((Label) block[i + 1]).getName();
					reusedLabel = true;
				}
				mBreakStack.push(currentBI);
				unstructureStatement(currentBI, s);
				mBreakStack.pop();
				/*
				 * Create break label unless no break occurred or we reused existing label
				 */
				if (!reusedLabel && currentBI.destLabel != null) {
					addLabel(new Label(s.getLocation(), currentBI.destLabel));
					mReachable = true;
				}
				currentBI.clear();
			}
		}
	}

	private Expression getLHSExpression(final LeftHandSide lhs) {
		Expression expr;
		if (lhs instanceof ArrayLHS) {
			final ArrayLHS arrlhs = (ArrayLHS) lhs;
			final Expression array = getLHSExpression(arrlhs.getArray());
			expr = new ArrayAccessExpression(lhs.getLocation(), lhs.getType(), array, arrlhs.getIndices());
		} else {
			final VariableLHS varlhs = (VariableLHS) lhs;
			expr = new IdentifierExpression(lhs.getLocation(), lhs.getType(), varlhs.getIdentifier(),
					varlhs.getDeclarationInformation());
		}
		return expr;
	}

	/**
	 * Converts a single statement to unstructured code. This may produce many new flat statements for example if
	 * statement is a while-loop.
	 *
	 * @param outer
	 *            The BreakInfo of the current statement. Used for if-then and while which may implicitly jump to the
	 *            end of the current statement.
	 * @param origStmt
	 *            The current statement that should be converted (not a label).
	 */
	private void unstructureStatement(final BreakInfo outer, final Statement origStmt) {
		if (origStmt instanceof GotoStatement) {
			new LoopEntryAnnotation(LoopEntryType.GOTO).annotate(origStmt);
			mFlatStatements.add(origStmt);
			mReachable = false;
		} else if (origStmt instanceof ReturnStatement) {
			mFlatStatements.add(origStmt);
			mReachable = false;
		} else if (origStmt instanceof BreakStatement) {
			String label = ((BreakStatement) origStmt).getLabel();
			if (label == null) {
				label = "*";
			}
			final BreakInfo dest = findLabel(label);
			if (dest.destLabel == null) {
				dest.destLabel = generateLabel();
			}
			final Statement newGotoStmt = new GotoStatement(origStmt.getLocation(), new String[] { dest.destLabel });
			new LoopExitAnnotation(LoopExitType.BREAK).annotate(newGotoStmt);
			postCreateStatement(origStmt, newGotoStmt);
			mReachable = false;
		} else if (origStmt instanceof WhileStatement) {
			final WhileStatement stmt = (WhileStatement) origStmt;
			final String head = generateLabel();
			final String body = generateLabel();
			String done;

			if (!(stmt.getCondition() instanceof WildcardExpression)) {
				done = generateLabel();
			} else {
				if (outer.destLabel == null) {
					outer.destLabel = generateLabel();
				}
				done = outer.destLabel;
			}

			// The label before the condition of the while loop gets the
			// location that represents the while loop.
			final ILocation loopLocation = new BoogieLocation(stmt.getLocation().getFileName(),
					stmt.getLocation().getStartLine(), stmt.getLocation().getEndLine(),
					stmt.getLocation().getStartColumn(), stmt.getLocation().getEndColumn());
			final Label l = new Label(loopLocation, head);
			new LoopEntryAnnotation(LoopEntryType.WHILE).annotate(l);
			addLabel(l);
			for (final LoopInvariantSpecification spec : stmt.getInvariants()) {
				if (spec.isFree()) {
					postCreateStatement(spec, new AssumeStatement(spec.getLocation(), spec.getFormula()));
				} else {
					postCreateStatement(spec, new AssertStatement(spec.getLocation(), spec.getFormula()));
				}
			}

			postCreateStatement(origStmt, new GotoStatement(origStmt.getLocation(), new String[] { body, done }));
			postCreateStatement(origStmt, new Label(origStmt.getLocation(), body));
			if (stmt.getCondition() instanceof WildcardExpression) {
				final AssumeStatement newCondStmt = new AssumeStatement(stmt.getLocation(),
						new BooleanLiteral(stmt.getCondition().getLocation(), BoogieType.TYPE_BOOL, true));
				new LoopEntryAnnotation(LoopEntryType.WHILE).annotate(newCondStmt);
				postCreateStatementFromCond(origStmt, newCondStmt, false);
			} else {
				final AssumeStatement newCondStmt = new AssumeStatement(stmt.getLocation(), stmt.getCondition());
				new LoopEntryAnnotation(LoopEntryType.WHILE).annotate(newCondStmt);
				postCreateStatementFromCond(origStmt, newCondStmt, false);
			}
			outer.breakLabels.add("*");
			unstructureBlock(stmt.getBody());
			if (mReachable) {
				postCreateStatement(origStmt, new GotoStatement(origStmt.getLocation(), new String[] { head }));
			}
			mReachable = false;

			if (!(stmt.getCondition() instanceof WildcardExpression)) {
				postCreateStatement(origStmt, new Label(origStmt.getLocation(), done));
				final AssumeStatement negatedCondStmt =
						new AssumeStatement(stmt.getLocation(), new UnaryExpression(stmt.getCondition().getLocation(),
								BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, stmt.getCondition()));
				new LoopExitAnnotation(LoopExitType.WHILE).annotate(negatedCondStmt);
				postCreateStatementFromCond(origStmt, negatedCondStmt, true);
				mReachable = true;
			}
		} else if (origStmt instanceof IfStatement) {
			final IfStatement stmt = (IfStatement) origStmt;
			final String thenLabel = generateLabel();
			final String elseLabel = generateLabel();
			postCreateStatement(origStmt, new GotoStatement(stmt.getLocation(), new String[] { thenLabel, elseLabel }));
			postCreateStatement(origStmt, new Label(origStmt.getLocation(), thenLabel));
			if (!(stmt.getCondition() instanceof WildcardExpression)) {
				postCreateStatementFromCond(origStmt, new AssumeStatement(stmt.getLocation(), stmt.getCondition()),
						false);
			}
			unstructureBlock(stmt.getThenPart());
			if (mReachable) {
				if (outer.destLabel == null) {
					outer.destLabel = generateLabel();
				}
				postCreateStatement(origStmt,
						new GotoStatement(origStmt.getLocation(), new String[] { outer.destLabel }));
			}
			mReachable = true;
			postCreateStatement(origStmt, new Label(origStmt.getLocation(), elseLabel));
			if (!(stmt.getCondition() instanceof WildcardExpression)) {
				postCreateStatementFromCond(origStmt,
						new AssumeStatement(stmt.getLocation(), new UnaryExpression(stmt.getCondition().getLocation(),
								BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, stmt.getCondition())),
						true);
			}
			unstructureBlock(stmt.getElsePart());
		} else if (origStmt instanceof AssignmentStatement) {
			final AssignmentStatement assign = (AssignmentStatement) origStmt;
			final LeftHandSide[] lhs = assign.getLhs();
			final Expression[] rhs = assign.getRhs();
			boolean changed = false;
			for (int i = 0; i < lhs.length; i++) {
				while (lhs[i] instanceof ArrayLHS) {
					final LeftHandSide array = ((ArrayLHS) lhs[i]).getArray();
					final Expression[] indices = ((ArrayLHS) lhs[i]).getIndices();
					final Expression arrayExpr = getLHSExpression(array);
					rhs[i] = new ArrayStoreExpression(lhs[i].getLocation(), array.getType(), arrayExpr, indices,
							rhs[i]);
					lhs[i] = array;
					changed = true;
				}
			}
			if (changed) {
				postCreateStatement(assign, new AssignmentStatement(assign.getLocation(), lhs, rhs));
			} else {
				mFlatStatements.add(origStmt);
			}
		} else {
			mFlatStatements.add(origStmt);
		}
	}

	/**
	 * Adds a new statement to the list of flat statements, add all annotations of the old statement, and remember it
	 * for backtranslation.
	 */
	private void postCreateStatement(final BoogieASTNode source, final Statement newStmt) {
		// adds annotations from old statement to new statement (if any)
		ModelUtils.copyAnnotations(source, newStmt);

		// adds new statement to list
		mFlatStatements.add(newStmt);

		// add mapping to backtranslation
		mTranslator.addMapping(source, newStmt);
	}

	private void postCreateStatementFromCond(final BoogieASTNode source, final AssumeStatement newStmt,
			final boolean isNegated) {
		postCreateStatement(source, newStmt);
		new ConditionAnnotation(isNegated).annotate(newStmt);
	}

	private String generateLabel() {
		return sLabelPrefix + mLabelNr++;
	}

	/**
	 * This class stores the information needed for breaking out of a block. Whenever a break to breakLabel is found, it
	 * is replaced by a goto to destLabel. If destLabel was not set at this time a new unique label is produced. If
	 * after analyzing a block destLabel is still not set, there is no break and the label does not need to be produced.
	 *
	 * @author hoenicke
	 *
	 */
	private static final class BreakInfo {
		Set<String> breakLabels = new HashSet<>();
		String destLabel;

		void clear() {
			breakLabels.clear();
			destLabel = null;
		}
	}
}
