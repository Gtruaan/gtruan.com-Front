import './assets/App.css';

import Header from './components/Header';
import CatCreationForm from './components/CatCreationForm';
import CatContainer from './components/CatList';

function App() {
    return (
        <>
            <Header />
            <CatCreationForm />
            <CatContainer />
        </>
    );
}

export default App;
