package de.uni_freiburg.informatik.ultimate.interactive;

import java.util.HashMap;
import java.util.Map;

public class ConverterRegistry<IA, IB> implements IConverterRegistry<IA, IB> {
	private final Map<Class<? extends IA>, IConverter<? extends IA, ? extends IB>> mapAB = new HashMap<>();
	private final Map<Class<? extends IB>, IConverter<? extends IB, ? extends IA>> mapBA = new HashMap<>();
	private final Map<Class<? extends IB>, IConverter<? extends IA, ? extends IB>> mapAB2 = new HashMap<>();
	private final Map<Class<? extends IA>, IConverter<? extends IB, ? extends IA>> mapBA2 = new HashMap<>();

	public ConverterRegistry() {
	}

	public void registerATypes(ITypeRegistry<IA> typeRegistry) {
		mapAB.keySet().forEach(typeRegistry::register);
		mapBA2.keySet().forEach(typeRegistry::register);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <A extends IA> IConverter<A, ? extends IB> getAB(Class<A> typeA) {
		return (IConverter<A, ? extends IB>) mapAB.get(typeA);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <B extends IB> IConverter<B, ? extends IA> getBA(Class<B> typeB) {
		return (IConverter<B, ? extends IA>) mapBA.get(typeB);
	}

	@Override
	public <B extends IB> IConverter<? extends IA, B> getAB2(Class<B> typeB) {
		return null;
	}

	@Override
	public <A extends IA> IConverter<? extends IB, A> getBA2(Class<A> typeA) {
		return null;
	}

	@Override
	public <A extends IA, B extends IB> void registerAB(IConverter<A, B> converter) {
		mapAB.put(converter.getTypeA(), converter);
		mapAB2.put(converter.getTypeB(), converter);
	}

	@Override
	public <A extends IA, B extends IB> void registerBA(IConverter<B, A> converter) {
		mapBA.put(converter.getTypeA(), converter);
		mapBA2.put(converter.getTypeB(), converter);
	}
}
