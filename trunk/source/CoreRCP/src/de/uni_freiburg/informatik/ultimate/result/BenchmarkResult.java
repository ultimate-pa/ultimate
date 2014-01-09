package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result that should be used to report benchmark informations like (e.g., 
 * runtime, number of iterations, size of automata, size of predicates, ...).
 * These benchmark informations are stored in the m_Benchmark object. The
 * toString() method of this object has do return the benchmark results in
 * human readable form.  
 * @author Matthias Heizmann
 */
public class BenchmarkResult<P> extends AbstractResult<P> {
	
	private final ILocation m_Location;
	private final String m_ShortDescrption;
	private final Object m_Benchmark;

	public BenchmarkResult(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence,
			ILocation m_Location, String m_ShortDescrption, Object m_Benchmark) {
		super(position, plugin, translatorSequence);
		this.m_Location = m_Location;
		this.m_ShortDescrption = m_ShortDescrption;
		this.m_Benchmark = m_Benchmark;
	}

	@Override
	public ILocation getLocation() {
		return m_Location;
	}

	@Override
	public String getShortDescription() {
		return m_ShortDescrption;
	}

	@Override
	public String getLongDescription() {
		return m_Benchmark.toString();
	}

}
