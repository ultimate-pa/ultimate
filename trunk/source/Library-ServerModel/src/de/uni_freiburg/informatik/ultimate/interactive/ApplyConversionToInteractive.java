package de.uni_freiburg.informatik.ultimate.interactive;

import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.interactive.IConverterRegistry.IConverter;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.UnregisteredTypeException;
import de.uni_freiburg.informatik.ultimate.interactive.utils.InheritanceUtil;

public class ApplyConversionToInteractive<M, O> implements IInteractive<M> {
	private IInteractive<O> mOriginal;
	private IConverterRegistry<O, M> mConverter;
	private Class<M> mTypeBound;

	public ApplyConversionToInteractive(IInteractive<O> original, IConverterRegistry<O, M> converter,
			Class<M> typeBound) {
		mOriginal = original;
		mConverter = converter;
		mTypeBound = typeBound;
	}

	@Override
	public <T extends M> void register(Class<T> type, Consumer<T> consumer) {
		IConverter<? extends O, T> converter = mConverter.getAB2(type);
		wrapRegister(converter, mOriginal, consumer);
	}

	private static <M, T> void wrapRegister(IConverter<M, T> src, IInteractive<? super M> old, Consumer<T> consumer) {
		old.register(src.getTypeA(), src.andThen(consumer));
	}

	@Override
	public <T extends M> void register(Class<T> type, Supplier<T> supplier) {
		IConverter<T, ? extends O> converter = mConverter.getBA(type);
		wrapRegister(converter, mOriginal, supplier);
	}

	private static <M, T> void wrapRegister(IConverter<T, M> src, IInteractive<? super M> old, Supplier<T> supplier) {
		old.register(src.getTypeB(), src.compose(supplier));
	}

	@Override
	public <D extends M, T extends M> void register(Class<T> type, Class<D> dataType, Function<D, T> supplier) {
		IConverter<T, ? extends O> converter = mConverter.getBA(type);
		IConverter<? extends O, D> dConverter = mConverter.getAB2(dataType);
		wrapRegister(type, dataType, converter, dConverter, supplier);
	}

	private <D extends M, T extends M, O1 extends O, O2 extends O> void wrapRegister(Class<T> type, Class<D> dataType,
			IConverter<T, O1> converter, IConverter<O2, D> dConverter, Function<D, T> supplier) {
		Function<O2, O1> f = d -> converter.apply(supplier.apply(dConverter.apply(d)));
		mOriginal.register(converter.getTypeB(), dConverter.getTypeA(), f);
	}

	@Override
	public void send(M data) {
		@SuppressWarnings("unchecked")
		Class<? extends M> type = (Class<? extends M>) data.getClass();
		IConverter<? extends M, ? extends O> converter;
		converter = mConverter.getBA(type);
		if (converter == null) {
			converter = InheritanceUtil.getInheritance(type, mTypeBound).stream().map(e -> mConverter.getBA(e))
					.filter(Objects::nonNull).findFirst().orElseThrow(() -> new UnregisteredTypeException(type));
		}
		wrapSend(converter, data);
	}

	@SuppressWarnings("unchecked")
	private <M1 extends M, T extends O> void wrapSend(IConverter<M1, T> src, M data) {
		mOriginal.send(src.apply((M1) data));
	}

	@Override
	public <T extends M> CompletableFuture<T> request(Class<T> type) {
		IConverter<? extends O, T> converter = mConverter.getAB2(type);
		return wrapRequest(converter);
	}

	private <O1 extends O, T extends M> CompletableFuture<T> wrapRequest(IConverter<O1, T> converter) {
		return mOriginal.request(converter.getTypeA()).thenApply(converter);
	}

	@Override
	public <T extends M> CompletableFuture<T> request(Class<T> type, M data) {
		IConverter<? extends O, T> converter = mConverter.getAB2(type);
		@SuppressWarnings("unchecked")
		Class<? extends M> dType = (Class<? extends M>) data.getClass();
		IConverter<? extends M, ? extends O> dConverter = mConverter.getBA(dType);
		return wrapRequest(converter, dConverter, data);
	}

	@SuppressWarnings("unchecked")
	private <O1 extends O, T extends M, D extends M, OD extends O> CompletableFuture<T> wrapRequest(
			IConverter<O1, T> converter, IConverter<D, OD> dConverter, M data) {
		return mOriginal.request(converter.getTypeA(), dConverter.apply((D) data)).thenApply(converter);
	}
}
