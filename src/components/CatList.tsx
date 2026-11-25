import '../assets/CatList.css';

import type { CatRecord } from '../cats';
import Cat from './Cat';

export type CatListState =
    | { status: 'loading' | 'error' }
    | { status: 'ready'; cats: CatRecord[] };

type CatListProps = {
    state: CatListState;
    onRetry: () => void;
};

export default function CatList({ state, onRetry }: CatListProps) {
    return (
        <section className='cat-gallery' aria-labelledby='cat-gallery-title'>
            <h2 id='cat-gallery-title'>Estxs son lxs gatxs que ha dejado la gente</h2>
            {state.status === 'loading' && (
                <div className='gallery-status' role='status'>
                    <img src='/assets/cat-icons/white.png' alt='' className='loading-image' width='50' height='50' />
                    <p>Cargando gatxs...</p>
                </div>
            )}
            {state.status === 'error' && (
                <div className='gallery-status'>
                    <p role='alert'>No se pudieron cargar lxs gatxs.</p>
                    <button className='button' type='button' onClick={onRetry}>Reintentar</button>
                </div>
            )}
            {state.status === 'ready' && (state.cats.length ? (
                <ul className='cat-list' role='list'>
                    {state.cats.map((cat) => <Cat key={cat.id} cat={cat} />)}
                </ul>
            ) : (
                <p className='gallery-status' role='status'>Todavía no hay gatxs.</p>
            ))}
        </section>
    );
}
