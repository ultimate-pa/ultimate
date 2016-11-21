package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTComment;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * PSTNode factory that creates ACLS comment nodes.
 */
public class ACSLNodeFactory extends DefaultNodeFactory {

	@Override
	public IPSTComment createComment(final ISourceRange location, final IASTComment comment) {
		final String text = mSource.getText(location);
		if (text.startsWith("/*@") || text.startsWith("//@")) {
			return new PSTACSLComment(mSource, location, comment);
		}
		return super.createComment(location, comment);
	}

}
