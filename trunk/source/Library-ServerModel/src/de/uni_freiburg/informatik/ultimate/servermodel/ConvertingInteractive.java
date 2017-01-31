package de.uni_freiburg.informatik.ultimate.servermodel;

import java.util.concurrent.CompletableFuture;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.servermodel.IConverterRegistry.IConverter;

public class ConvertingInteractive<M, O> implements IInteractive<M> {
	private IInteractive<O> mOriginal;
	private IConverterRegistry<O, M> mConverter;

	public ConvertingInteractive(IInteractive<O> original, IConverterRegistry<O, M> converter) {
		mOriginal = original;
		mConverter = converter;
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
		// TODO Auto-generated method stub

	}

	@Override
	public void send(M data) {
		@SuppressWarnings("unchecked")
		Class<? extends M> type = (Class<? extends M>) data.getClass();
		IConverter<? extends M, ? extends O> converter = mConverter.getBA(type);
		wrapSend(converter, mOriginal, type.cast(data));
		// mOriginal.send(converter.apply(type.cast(data)));
	}

	private static <M, T> void wrapSend(IConverter<M, T> src, IInteractive<? super T> old, Object data) {
		old.send(src.apply(src.getTypeA().cast(data)));
	}

	@Override
	public <T extends M> CompletableFuture<T> request(Class<T> type, M data) {
		// TODO Auto-generated method stub
		return null;
	}

}
