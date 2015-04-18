package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;

/**
 * Value for backtranslation mappings.
 * See documentation of getters, for more information.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BackTransValue {

	private String mInlineEntryProcId;
	private BoogieASTNode mOriginalNode;
	private Deque<CallStatement> mOriginalCallStack;

	public BackTransValue(String inlineEntryProcId,  Deque<CallStatement> origCallStack, BoogieASTNode origNode) {
		mInlineEntryProcId = inlineEntryProcId;
		mOriginalNode = origNode;
		mOriginalCallStack = origCallStack;
	}

	/** @return Identifier from the Procedure, where the inlining process started. */
	public String getInlineEntryProcId() {
		return mInlineEntryProcId;
	}

	/** 
	 * Returns the stack of original CallStatements, that created the key while inlining.
	 * <p>
	 * The topmost call from the stack is the last/innermost call.<br>
	 * The stack is empty, iff the key was direct part of the entry procedure from the inlining process.
	 * <p>
	 * Reference equality of the stacks and the calls inside the stacks is ensured.
	 * <p>
	 * <b>Don't modify</b> the returned stacks!
	 * 
	 * @return Original call stack.
	 */
	public Deque<CallStatement> getOriginalCallStack() {
		return mOriginalCallStack;
	}

	/**  @return Backtranslated node. {@code null} if the node should be omitted. */
	public BoogieASTNode getOriginalNode() {
		return mOriginalNode;
	}
	
	
	
}
