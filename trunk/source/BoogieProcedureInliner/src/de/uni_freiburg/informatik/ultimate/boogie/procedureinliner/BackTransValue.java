package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

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
	private CallStatement mOriginalCall;
	private BoogieASTNode mOriginalNode;

	public BackTransValue(String inlineEntryProcId, BoogieASTNode originalNode, CallStatement originalCall) {
		mInlineEntryProcId = inlineEntryProcId;
		mOriginalNode = originalNode;
		mOriginalCall = originalCall;
	}

	/** @return Identifier from the Procedure, where the inlining process started. */
	public String getInlineEntryProcId() {
		return mInlineEntryProcId;
	}

	/** 
	 * @return Original CallStatement, which was inlined and generated the key.
	 *         null, if key wasn't generated from an inlined call (which means, it was part of the inline entry point).
	 */
	public CallStatement getOriginalCall() {
		return mOriginalCall;
	}

	/**  @return Original BoogieASTNode, which generated the key  while inlining. */
	public BoogieASTNode getOriginalNode() {
		return mOriginalNode;
	}
	
	
	
}
