package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Deque;
import java.util.List;

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

	// TODO update documentation
	/** 
	 * @return Original CallStatement, which was inlined and generated the key.
	 *         null, if key wasn't generated from an inlined call (which means, it was part of the inline entry point).
	 */
	public Deque<CallStatement> getOriginalCallStack() {
		return mOriginalCallStack;
	}

	/**  @return Original BoogieASTNode, which generated the key  while inlining. */
	public BoogieASTNode getOriginalNode() {
		return mOriginalNode;
	}
	
	
	
}
