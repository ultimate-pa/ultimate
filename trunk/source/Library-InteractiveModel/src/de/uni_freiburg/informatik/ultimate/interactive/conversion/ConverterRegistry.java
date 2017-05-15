package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;

public class ConverterRegistry<IA, IB> implements IConverterRegistry<IA, IB> {
	private final Map<Class<? extends IA>, IConverter<? extends IA, ? extends IB>> mapAB = new HashMap<>();
	private final Map<Class<? extends IB>, IConverter<? extends IB, ? extends IA>> mapBA = new HashMap<>();
	private final Map<Class<? extends IB>, IConverter<? extends IA, ? extends IB>> mapAB2 = new HashMap<>();
	private final Map<Class<? extends IA>, IConverter<? extends IB, ? extends IA>> mapBA2 = new HashMap<>();
	private final Map<Class<? extends IB>, Map<Class<? extends IB>, IResponseConverter<? extends IA, ? extends IB, ? extends IB>>> mapRC =
			new HashMap<>();

	public void registerATypes(final ITypeRegistry<IA> typeRegistry) {
		mapAB.keySet().forEach(typeRegistry::register);
		mapBA2.keySet().forEach(typeRegistry::register);
		mapRC.values()
				.forEach(m -> m.values().stream().map(IResponseConverter::getTypeA).forEach(typeRegistry::register));
	}

	@SuppressWarnings("unchecked")
	@Override
	public <A extends IA> IConverter<A, ? extends IB> getAB(final Class<A> typeA) {
		return (IConverter<A, ? extends IB>) mapAB.get(typeA);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <B extends IB> IConverter<B, ? extends IA> getBA(final Class<B> typeB) {
		return (IConverter<B, ? extends IA>) mapBA.get(typeB);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <B extends IB> IConverter<? extends IA, B> getAB2(final Class<B> typeB) {
		return (IConverter<? extends IA, B>) mapAB2.get(typeB);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <A extends IA> IConverter<? extends IB, A> getBA2(final Class<A> typeA) {
		return (IConverter<? extends IB, A>) mapBA2.get(typeA);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <B extends IB, D extends IB> IResponseConverter<? extends IA, D, B> getRConv(final Class<B> typeB,
			final Class<D> typeD) {
		final Map<Class<? extends IB>, IResponseConverter<? extends IA, ? extends IB, ? extends IB>> mapRC2 =
				mapRC.get(typeB);
		if (mapRC2 == null)
			return null;
		return (IResponseConverter<? extends IA, D, B>) mapRC2.get(typeD);
	}

	@Override
	public <A extends IA, B extends IB> void registerAB(final IConverter<A, B> converter) {
		mapAB.put(converter.getTypeA(), converter);
		mapAB2.put(converter.getTypeB(), converter);
	}

	@Override
	public <A extends IA, B extends IB> void registerBA(final IConverter<B, A> converter) {
		mapBA.put(converter.getTypeA(), converter);
		mapBA2.put(converter.getTypeB(), converter);
	}

	@Override
	public <A extends IA, D extends IB, B extends IB> void
			registerRConv(final IResponseConverter<A, D, B> responseConverter) {
		final Class<B> typeB = responseConverter.getTypeB();
		final Map<Class<? extends IB>, IResponseConverter<? extends IA, ? extends IB, ? extends IB>> mapRC2;
		if (mapRC.containsKey(typeB)) {
			mapRC2 = mapRC.get(typeB);
		} else {
			mapRC2 = new HashMap<>();
			mapRC.put(typeB, mapRC2);
		}

		mapRC2.put(responseConverter.getTypeData(), responseConverter);
	}
}
