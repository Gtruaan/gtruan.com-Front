import '../assets/CatList.css';

import { useEffect, useState } from 'react';
import Cat from './Cat';
import API_URL from '../config';


export default function CatContainer() {
    const [catContainer, setCatContainer] = useState({
        loaded: false,
        cats: []
    });
    useEffect(() => {
        fetch(API_URL, {
            method: 'GET',
            headers: {
                'Content-Type': 'application/json'
            }
        }).then(res => res.json()
            .then(result => {
                // removing shuffle for now
                // result.sort(() => Math.random() - 0.5);
                result.reverse();
                setCatContainer({
                    loaded: true,
                    cats: result
                });
            }) 
        );
    }, []);

    return (
        <div>
            <h3>Estxs son lxs gatxs que ha dejado la gente</h3>
            {catContainer.loaded && 
            <div className='cat-container'>
                {catContainer.loaded && catContainer.cats?.map(
                    (cat) => <Cat key={cat.id}
                        catName={cat.name}
                        creationDate={new Date(cat.creation)}
                        variation={cat.variation} 
                    />
                )}
            </div>
            }
            {!catContainer.loaded &&
            <>
                <img src='/assets/cat-icons/white.png' 
                    alt='loading'
                    className='loading-image'
                />
                <p>Cargando gatxs...</p>
            </>
            } 
        </div>
    );
}