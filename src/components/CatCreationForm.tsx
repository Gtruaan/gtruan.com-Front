import '../assets/CatCreation.css';

import { useRef, useState } from 'react';
import type { FormEvent } from 'react';
import { createCat } from '../cats';

const variations = [
    { value: 'black', label: 'Negro' },
    { value: 'tabby', label: 'Tabby' },
    { value: 'orange', label: 'Naranja' },
    { value: 'white', label: 'Blanco' },
    { value: 'calico', label: 'Calico' },
];

const defaultVariation = 'tabby';

export default function CatCreationForm({ onCreated }: { onCreated: () => void }) {
    const dialog = useRef<HTMLDialogElement>(null);
    const nameInput = useRef<HTMLInputElement>(null);
    const [variation, setVariation] = useState(defaultVariation);
    const [name, setName] = useState('');
    const [isSubmitting, setIsSubmitting] = useState(false);
    const [error, setError] = useState('');

    function openDialog() {
        dialog.current?.showModal();
        nameInput.current?.focus();
    }

    async function handleSubmit(event: FormEvent<HTMLFormElement>) {
        event.preventDefault();

        if (isSubmitting || !name.trim()) {
            return;
        }

        setIsSubmitting(true);
        setError('');

        try {
            await createCat({ name: name.trim(), variation });
        } catch {
            setError('No se pudo crear el gato. Inténtalo de nuevo.');
            return;
        } finally {
            setIsSubmitting(false);
        }

        dialog.current?.close();
        setName('');
        setVariation(defaultVariation);
        onCreated();
    }

    return (
        <>
            <button className='button create-button' type='button' onClick={openDialog}>
                Crear gato
            </button>
            <dialog
                className='cat-dialog'
                ref={dialog}
                aria-labelledby='cat-dialog-title'
                onClick={(event) => {
                    if (event.target === event.currentTarget) {
                        event.currentTarget.close();
                    }
                }}
            >
                <form className='cat-form' onSubmit={handleSubmit}>
                    <div className='cat-form-header'>
                        <h2 id='cat-dialog-title'>Crear gato</h2>
                        <button
                            className='button close-button'
                            type='button'
                            aria-label='Cerrar'
                            onClick={() => dialog.current?.close()}
                        >
                            ×
                        </button>
                    </div>
                    <img
                        className='cat-preview'
                        src={`/assets/cat-icons/${variation}.png`}
                        alt=''
                        width='180'
                        height='180'
                    />
                    <label>
                        Color
                        <select
                            value={variation}
                            onChange={(event) => setVariation(event.currentTarget.value)}
                            disabled={isSubmitting}
                        >
                            {variations.map(({ value, label }) => (
                                <option key={value} value={value}>{label}</option>
                            ))}
                        </select>
                    </label>
                    <label>
                        Nombre
                        <input
                            ref={nameInput}
                            type='text'
                            value={name}
                            onChange={(event) => setName(event.currentTarget.value)}
                            required
                            disabled={isSubmitting}
                        />
                    </label>
                    <button className='button confirm-button' disabled={isSubmitting || !name.trim()}>
                        {isSubmitting ? 'Guardando...' : 'Confirmar'}
                    </button>
                    {error && <p className='form-error' role='alert'>{error}</p>}
                </form>
            </dialog>
        </>
    );
}
