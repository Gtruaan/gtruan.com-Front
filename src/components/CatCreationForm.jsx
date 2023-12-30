import '../assets/CatCreation.css';

import Modal from 'react-modal';
import { useState } from 'react';
import API_URL from '../config';


function postCat(cat) {
    fetch(API_URL, {
        method: 'POST',
        headers: {
            'Content-Type': 'application/json'
        },
        body: JSON.stringify(cat)
    }).then(res => res.json().then(
        () => window.location.reload()
    )
    );
}

export default function CatCreationForm() {
    const [isOpen, setIsOpen] = useState(false);

    const [variation, setVariation] = useState('tabby');
    const [name, setName] = useState('');

    const handleVariationChange = (event) => {
        setVariation(event.target.value);
    };

    const handleNameChange = (event) => {
        setName(event.target.value);
    };

    const handleConfirmation = () => {
        if (name != '') {
            postCat({
                'name': name,
                'variation': variation
            });
            setIsOpen(false);
        }
    };

    return (
        <>
            <button type='button' onClick={() => setIsOpen(true)}>
            Crear gato
            </button>
            {isOpen && (
                <Modal className='cat-creation-form' 
                    isOpen={isOpen} 
                    onRequestClose={() => setIsOpen(false)}
                    overlayClassName='cat-creation-form-backdrop'>
                    <span className='cat-creation-form-close-button'
                        onClick={() => setIsOpen(false)}>
                        X
                    </span>
                    <img className='cat-creation-form-image' 
                        src={`/assets/cat-icons/${variation}.png`} 
                        alt={variation} />
                    <select className='cat-variation-input' 
                        defaultValue={variation} 
                        onChange={handleVariationChange}>
                        <option value='black'>Black</option>
                        <option value='tabby'>Tabby</option>
                        <option value='orange'>Naranja</option>
                        <option value='white'>Blanco</option>
                        <option value='calico'>Calico</option>
                    </select>
                    <input type='text' 
                        className='cat-name-input'
                        placeholder='Nombre'
                        onChange={handleNameChange} />
                    <button type='button' onClick={handleConfirmation}
                        className='cat-confirm-button'>
                        Confirmar
                    </button>
                </Modal>
            )}
        </>
    );
}
