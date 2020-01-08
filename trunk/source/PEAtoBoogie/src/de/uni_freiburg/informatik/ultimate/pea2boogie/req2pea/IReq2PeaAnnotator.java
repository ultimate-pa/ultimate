package de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;

public interface IReq2PeaAnnotator {

	public List<Statement> getStateChecks();

	public PeaResultUtil getPeaResultUtil();

	public List<Statement> getPreChecks();

}
