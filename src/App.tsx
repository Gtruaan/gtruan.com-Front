import './assets/App.css';

import { useEffect, useState } from 'react';
import Header from './components/Header';
import CatCreationForm from './components/CatCreationForm';
import CatList from './components/CatList';
import type { CatListState } from './components/CatList';
import { getCats } from './cats';

function App() {
    const [state, setState] = useState<CatListState>({ status: 'loading' });
    const [reloadCount, setReloadCount] = useState(0);

    useEffect(() => {
        const controller = new AbortController();

        getCats(controller.signal).then(
            (cats) => {
                if (!controller.signal.aborted) {
                    setState({ status: 'ready', cats });
                }
            },
            () => {
                if (!controller.signal.aborted) {
                    setState({ status: 'error' });
                }
            },
        );

        return () => controller.abort();
    }, [reloadCount]);

    function reloadCats() {
        setState({ status: 'loading' });
        setReloadCount((count) => count + 1);
    }

    return (
        <main className='page'>
            <Header />
            <CatCreationForm onCreated={reloadCats} />
            <CatList state={state} onRetry={reloadCats} />
        </main>
    );
}

export default App;
