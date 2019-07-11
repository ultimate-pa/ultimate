package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public interface IReqSymbolTable {

	public IdentifierExpression getIdentifierExpression(final String name);

	public String getPcName(PhaseEventAutomata automaton);

	public Set<String> getConstVars();

	public Set<String> getPrimedVars();

	public Set<String> getEventVars();

	public String getDeltaVarName();

	public VariableLHS getVariableLhs(String clockVar);

	public Collection<String> getClockVars();

	public Collection<String> getStateVars();

	public String getPrimedVarId(String stateVar);

	public Collection<? extends String> getPcVars();

	public Collection<? extends Declaration> getDeclarations();

	public Map<PatternType, BoogieLocation> getLocations();

	public Map<String, Expression> getConstToValue();
}
